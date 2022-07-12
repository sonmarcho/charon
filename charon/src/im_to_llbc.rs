//! IM to LLBC (Control-Flow Internal MIR)
//!
//! The reconstruction algorithm is not written to be efficient (its complexity
//! is probably very bad), but it was not written to be: this is still an early
//! stage and we want the algorithm to generate the best reconstruction as
//! possible. We still need to test the algorithm on more interesting examples,
//! and will consider making it more efficient once it is a bit mature and well
//! tested.
//! Also note that we more importantly focus on making the algorithm sound: the
//! reconstructed program must always be equivalent to the original MIR program,
//! and the fact that the reconstruction preserves this property must be obvious.
//!
//! Finally, we conjecture the execution time shouldn't be too much a problem:
//! we don't expect the translation mechanism to be applied on super huge functions
//! (which will be difficult to formally analyze), and the MIR graphs are actually
//! not that big because statements are grouped into code blocks (a block is made
//! of a list of statements, followed by a terminator - branchings and jumps can
//! only be performed by terminators -, meaning that MIR graphs don't have that
//! many nodes and edges).

use crate::im_ast::FunDeclId;
use crate::im_ast::{self as src, GlobalDeclId};
use crate::llbc_ast as tgt;
use crate::types::TypeDecls;
use crate::values as v;
use hashlink::linked_hash_map::LinkedHashMap;
use im;
use im::Vector;
use petgraph::algo::floyd_warshall::floyd_warshall;
use petgraph::algo::toposort;
use petgraph::graphmap::DiGraphMap;
use petgraph::Direction;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::iter::FromIterator;

pub type Defs = (tgt::FunDecls, tgt::GlobalDecls);

/// Control-Flow Graph
type Cfg = DiGraphMap<src::BlockId::Id, ()>;

fn get_block_targets(body: &src::ExprBody, block_id: src::BlockId::Id) -> Vec<src::BlockId::Id> {
    let block = body.body.get(block_id).unwrap();

    match &block.terminator {
        src::Terminator::Goto { target }
        | src::Terminator::Drop { place: _, target }
        | src::Terminator::Call {
            func: _,
            region_args: _,
            type_args: _,
            args: _,
            dest: _,
            target,
        }
        | src::Terminator::Assert {
            cond: _,
            expected: _,
            target,
        } => {
            vec![*target]
        }
        src::Terminator::Switch { discr: _, targets } => targets.get_targets(),
        src::Terminator::Panic | src::Terminator::Unreachable | src::Terminator::Return => {
            vec![]
        }
    }
}

/// This structure contains various information about a function's CFG.
struct CfgPartialInfo {
    /// The CFG
    pub cfg: Cfg,
    /// The CFG where all the backward edges have been removed
    pub cfg_no_be: Cfg,
    /// We consider the destination of the backward edges to be loop entries and
    /// store them here.
    pub loop_entries: HashSet<src::BlockId::Id>,
    /// The backward edges
    pub backward_edges: HashSet<(src::BlockId::Id, src::BlockId::Id)>,
    /// The blocks whose terminators are a switch are stored here.
    pub switch_blocks: HashSet<src::BlockId::Id>,
}

/// Similar to `CfgPartialInfo`, but with more information
struct CfgInfo {
    pub cfg: Cfg,
    pub cfg_no_be: Cfg,
    pub loop_entries: HashSet<src::BlockId::Id>,
    pub backward_edges: HashSet<(src::BlockId::Id, src::BlockId::Id)>,
    pub switch_blocks: HashSet<src::BlockId::Id>,
    /// The reachability matrix:
    /// src can reach dest <==> (src, dest) in reachability
    /// TODO: this is not necessary anymore. There is a place where we use it
    /// as a test to shortcut some computations, but computing this matrix
    /// is actually probably too expensive for the shortcut to be useful...
    pub reachability: HashSet<(src::BlockId::Id, src::BlockId::Id)>,
}

/// Build the CFGs (the "regular" CFG and the CFG without backward edges) and
/// compute some information like the loop entries and the switch blocks.
fn build_cfg_partial_info(body: &src::ExprBody) -> CfgPartialInfo {
    let mut cfg = CfgPartialInfo {
        cfg: Cfg::new(),
        cfg_no_be: Cfg::new(),
        loop_entries: HashSet::new(),
        backward_edges: HashSet::new(),
        switch_blocks: HashSet::new(),
    };

    // Add the nodes
    for block_id in body.body.iter_indices() {
        cfg.cfg.add_node(block_id);
        cfg.cfg_no_be.add_node(block_id);
    }

    // Add the edges
    let ancestors = im::HashSet::new();
    let mut explored = im::HashSet::new();
    build_cfg_partial_info_edges(
        &mut cfg,
        &ancestors,
        &mut explored,
        body,
        src::BlockId::ZERO,
    );

    cfg
}

fn block_is_switch(body: &src::ExprBody, block_id: src::BlockId::Id) -> bool {
    let block = body.body.get(block_id).unwrap();
    block.terminator.is_switch()
}

fn build_cfg_partial_info_edges(
    cfg: &mut CfgPartialInfo,
    ancestors: &im::HashSet<src::BlockId::Id>,
    explored: &mut im::HashSet<src::BlockId::Id>,
    body: &src::ExprBody,
    block_id: src::BlockId::Id,
) {
    // Check if we already explored the current node
    if explored.contains(&block_id) {
        return;
    }
    explored.insert(block_id);

    // Insert the current block in the set of ancestors blocks
    let mut ancestors = ancestors.clone();
    ancestors.insert(block_id);

    // Check if it is a switch
    if block_is_switch(body, block_id) {
        cfg.switch_blocks.insert(block_id);
    }

    // Retrieve the block targets
    let targets = get_block_targets(body, block_id);

    // Add edges for all the targets and explore them, if they are not predecessors
    for tgt in &targets {
        // Insert the edge in the "regular" CFG
        cfg.cfg.add_edge(block_id, *tgt, ());

        // We need to check if it is a backward edge before inserting it in the
        // CFG without backward edges and exploring it
        if ancestors.contains(tgt) {
            // This is a backward edge
            cfg.loop_entries.insert(*tgt);
            cfg.backward_edges.insert((block_id, *tgt));
        } else {
            // Not a backward edge: insert the edge and explore
            cfg.cfg_no_be.add_edge(block_id, *tgt, ());
            build_cfg_partial_info_edges(cfg, &ancestors, explored, body, *tgt);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct OrdBlockId {
    id: src::BlockId::Id,
    /// The rank in the topological order
    rank: usize,
}

impl Ord for OrdBlockId {
    fn cmp(&self, other: &Self) -> Ordering {
        self.rank.cmp(&other.rank)
    }
}

impl PartialOrd for OrdBlockId {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Compute the reachability matrix for a graph.
///
/// We represent the reachability matrix as a set such R that:
/// there exists a path from src to dest <==> (src, dest) in R
fn compute_reachability(cfg: &CfgPartialInfo) -> HashSet<(src::BlockId::Id, src::BlockId::Id)> {
    // We simply use Floyd-Warshall.
    // We just need to be a little careful: we have to make sure the value we
    // use for infinity is never reached. That is to say, that there are stricly
    // less edges in the graph than usize::MAX.
    // Note that for now, the assertion will actually always statically succeed,
    // because `edge_count` returns a usize...
    // Also, if we have as many edges as usize::MAX, the computer will probably
    // be out of memory...
    // It still is good to keep it there.
    assert!(cfg.cfg.edge_count() < std::usize::MAX);

    let fw_matrix: HashMap<(src::BlockId::Id, src::BlockId::Id), usize> =
        floyd_warshall(&cfg.cfg, &|_| 1).unwrap();

    // Convert the fw_matrix
    let reachability: HashSet<(src::BlockId::Id, src::BlockId::Id)> =
        HashSet::from_iter(fw_matrix.into_iter().filter_map(|((src, dst), dest)| {
            if dest == std::usize::MAX {
                None
            } else {
                Some((src, dst))
            }
        }));

    reachability
}

fn compute_cfg_info_from_partial(cfg: CfgPartialInfo) -> CfgInfo {
    let reachability = compute_reachability(&cfg);

    let CfgPartialInfo {
        cfg,
        cfg_no_be,
        loop_entries,
        backward_edges,
        switch_blocks,
    } = cfg;

    CfgInfo {
        cfg,
        cfg_no_be,
        loop_entries,
        backward_edges,
        switch_blocks,
        reachability,
    }
}

#[derive(Debug, Clone)]
struct LoopExitCandidateInfo {
    /// The occurrences going to this exit.
    /// For every occurrence, we register the distance between the loop entry
    /// and the node from which the edge going to the exit starts.
    /// If later we have to choose between candidates with the same number
    /// of occurrences, we choose the one with the smallest distances.
    ///
    /// Note that it *may* happen that we have several exit candidates referenced
    /// more than once for one loop. This comes from the fact that whenever we
    /// reach a node from which the loop entry is not reachable (without using a
    /// backward edge leading to an outer loop entry), we register this node
    /// as well as all its children as exit candidates.
    /// Consider the following example:
    /// ```
    /// while i < max {
    ///     if cond {
    ///         break;
    ///     }
    ///     s += i;
    ///     i += 1
    /// }
    /// // All the below nodes are exit candidates (each of them is referenced twice)
    /// s += 1;
    /// return s;
    /// ```
    pub occurrences: Vec<usize>,
}

/// Check if a loop entry is reachable from a node, in a graph where we remove
/// the backward edges going directly to the loop entry.
///
/// If the loop entry is not reachable, it means that:
/// - the loop entry is not reachable at all
/// - or it is only reachable through an outer loop
///
/// The starting node should be a (transitive) child of the loop entry.
/// We use this to find candidates for loop exits.
fn loop_entry_is_reachable_from_inner(
    cfg: &CfgInfo,
    loop_entry: src::BlockId::Id,
    block_id: src::BlockId::Id,
) -> bool {
    // Shortcut: the loop entry is not reachable at all
    if !cfg.reachability.contains(&(block_id, loop_entry)) {
        return false;
    }

    // It is reachable in the complete graph. Check if it is reachable by not
    // going through backward edges which go to outer loops. In practice, we
    // just need to forbid the use of any backward edges at the exception of
    // those which go directly to the current loop's entry. This means that we
    // ignore backward edges to outer loops of course, but also backward edges
    // to inner loops because we shouldn't need to follow those (there should be
    // more direct paths).

    // Explore the graph starting at block_id
    let mut explored: HashSet<src::BlockId::Id> = HashSet::new();
    let mut stack: VecDeque<src::BlockId::Id> = VecDeque::new();
    stack.push_back(block_id);
    while !stack.is_empty() {
        let bid = stack.pop_front().unwrap();
        if explored.contains(&bid) {
            continue;
        }
        explored.insert(bid);

        let next_ids = cfg.cfg.neighbors_directed(bid, Direction::Outgoing);
        for next_id in next_ids {
            // Check if this is a backward edge
            if cfg.backward_edges.contains(&(bid, next_id)) {
                // Backward edge: only allow those going directly to the current
                // loop's entry
                if next_id == loop_entry {
                    // The loop entry is reachable
                    return true;
                } else {
                    // Forbidden edge: ignore
                    continue;
                }
            } else {
                // Nothing special: add the node to the stack for further
                // exploration
                stack.push_back(next_id);
            }
        }
    }

    // The loop entry is not reachable
    return false;
}

struct FilteredLoopParents {
    remaining_parents: Vector<(src::BlockId::Id, usize)>,
    removed_parents: Vector<(src::BlockId::Id, usize)>,
}

fn filter_loop_parents(
    cfg: &CfgInfo,
    parent_loops: &Vector<(src::BlockId::Id, usize)>,
    block_id: src::BlockId::Id,
) -> Option<FilteredLoopParents> {
    let mut eliminate: usize = 0;
    for (loop_id, _ldist) in parent_loops.iter().rev() {
        if !loop_entry_is_reachable_from_inner(cfg, *loop_id, block_id) {
            eliminate += 1;
        } else {
            break;
        }
    }

    if eliminate > 0 {
        // Split the vector of parents
        let (mut remaining_parents, removed_parents) = parent_loops
            .clone()
            .split_at(parent_loops.len() - eliminate);
        //        let removed_parents = Vector::from_iter(removed_parents.into_iter().map(|(bid, _)| bid));

        // Update the distance to the last loop - we just increment the distance
        // by 1, because from the point of view of the parent loop, we just exited
        // a block and go to the next sequence of instructions.
        if !remaining_parents.is_empty() {
            remaining_parents
                .get_mut(remaining_parents.len() - 1)
                .unwrap()
                .1 += 1;
        }

        Some(FilteredLoopParents {
            remaining_parents,
            removed_parents,
        })
    } else {
        None
    }
}

/// List the nodes reachable from a starting point.
/// We list the nodes and the depth (in the AST) at which they were found.
fn list_reachable(cfg: &Cfg, start: src::BlockId::Id) -> HashMap<src::BlockId::Id, usize> {
    let mut reachable: HashMap<src::BlockId::Id, usize> = HashMap::new();
    let mut stack: VecDeque<(src::BlockId::Id, usize)> = VecDeque::new();
    stack.push_back((start, 0));

    while !stack.is_empty() {
        let (bid, dist) = stack.pop_front().unwrap();

        // Ignore this node if we already registered it with a better distance
        match reachable.get(&bid) {
            None => (),
            Some(original_dist) => {
                if *original_dist < dist {
                    continue;
                }
            }
        }

        // Inset the node with its distance
        reachable.insert(bid, dist);

        // Add the children to the stack
        for child in cfg.neighbors(bid) {
            stack.push_back((child, dist + 1));
        }
    }

    // Return
    return reachable;
}

/// Register a node and its children as exit candidates for a list of
/// parent loops.
fn register_children_as_loop_exit_candidates(
    cfg: &CfgInfo,
    loop_exits: &mut HashMap<
        src::BlockId::Id,
        LinkedHashMap<src::BlockId::Id, LoopExitCandidateInfo>,
    >,
    removed_parent_loops: &Vector<(src::BlockId::Id, usize)>,
    block_id: src::BlockId::Id,
) {
    // List the reachable nodes
    let reachable = list_reachable(&cfg.cfg_no_be, block_id);

    let mut base_dist = 0;
    // For every parent loop, in reverse order (we go from last to first in
    // order to correctly compute the distances)
    for (loop_id, loop_dist) in removed_parent_loops.iter().rev() {
        // Update the distance to the loop entry
        base_dist += *loop_dist;

        // Retrieve the candidates
        let candidates = loop_exits.get_mut(loop_id).unwrap();

        // Update them
        for (bid, dist) in reachable.iter() {
            let distance = base_dist + *dist;
            match candidates.get_mut(bid) {
                None => {
                    candidates.insert(
                        *bid,
                        LoopExitCandidateInfo {
                            occurrences: vec![distance],
                        },
                    );
                }
                Some(c) => {
                    c.occurrences.push(distance);
                }
            }
        }
    }
}

/// Compute the loop exit candidates.
///
/// There may be several candidates with the same "optimality" (same number of
/// occurrences, etc.), in which case we choose the first one which was registered
/// (the order in which we explore the graph is deterministic): this is why we
/// store the candidates in a linked hash map.
fn compute_loop_exit_candidates(
    cfg: &CfgInfo,
    explored: &mut HashSet<src::BlockId::Id>,
    ordered_loops: &mut Vec<src::BlockId::Id>,
    loop_exits: &mut HashMap<
        src::BlockId::Id,
        LinkedHashMap<src::BlockId::Id, LoopExitCandidateInfo>,
    >,
    // List of parent loops, with the distance to the entry of the loop (the distance
    // is the distance between the current node and the loop entry for the last parent,
    // and the distance between the parents for the others).
    mut parent_loops: Vector<(src::BlockId::Id, usize)>,
    block_id: src::BlockId::Id,
) {
    if explored.contains(&block_id) {
        return;
    }
    explored.insert(block_id);

    // Check if we enter a loop - add the corresponding node if necessary
    if cfg.loop_entries.contains(&block_id) {
        parent_loops.push_back((block_id, 1));
        ordered_loops.push(block_id);
    } else {
        // Increase the distance with the parent loop
        if !parent_loops.is_empty() {
            parent_loops.get_mut(parent_loops.len() - 1).unwrap().1 += 1;
        }
    };

    // Retrieve the children - note that we ignore the back edges
    let children = cfg.cfg_no_be.neighbors(block_id);
    for child in children {
        // If the parent loop entry is not reachable from the child without going
        // through a backward edge which goes directly to the loop entry, consider
        // this node a potential exit.
        match filter_loop_parents(cfg, &parent_loops, child) {
            None => {
                compute_loop_exit_candidates(
                    cfg,
                    explored,
                    ordered_loops,
                    loop_exits,
                    parent_loops.clone(),
                    child,
                );
            }
            Some(fparent_loops) => {
                // We filtered some parent loops: it means this child and its
                // children are loop exit candidates for all those loops: we must
                // thus register them.
                // Note that we register the child *and* its children: the reason
                // is that we might do something *then* actually jump to the exit.
                // For instance, the following block of code:
                // ```
                // if cond { break; } else { ... }
                // ```
                //
                // Gets translated in MIR to something like this:
                // ```
                // bb1: {
                //   if cond -> bb2 else -> bb3; // bb2 is not the real exit
                // }
                //
                // bb2: {
                //   goto bb4; // bb4 is the real exit
                // }
                // ```
                register_children_as_loop_exit_candidates(
                    cfg,
                    loop_exits,
                    &fparent_loops.removed_parents,
                    child,
                );

                // Explore, with the filtered parents
                compute_loop_exit_candidates(
                    cfg,
                    explored,
                    ordered_loops,
                    loop_exits,
                    fparent_loops.remaining_parents,
                    child,
                );
            }
        }
    }
}

/// See [`compute_loop_switch_exits`](compute_loop_switch_exits) for
/// explanations about what "exits" are.
///
/// The following function computes the loop exits. It acts as follows.
///
/// We keep track of a stack of the loops in which we entered.
/// It is very easy to check when we enter a loop: loop entries are destinations
/// of backward edges, which can be spotted with a simple graph exploration (see
/// [`build_cfg_partial_info`](build_cfg_partial_info).
/// The criteria to consider whether we exit a loop is the following:
/// - we exit a loop if we go to a block from which we can't reach the loop
///   entry at all
/// - or if we can reach the loop entry, but must use a backward edge which goes
///   to an outer loop
///
/// It is better explained on the following example:
/// ```
/// 'outer while i < max {
///     'inner while j < max {
///        j += 1;
///     }
///     // (i)
///     i += 1;
/// }
/// ```
/// If we enter the inner loop then go to (i) from the inner loop, we consider
/// that we exited the outer loop because:
/// - we can reach the entry of the inner loop from (i) (by finishing then
///   starting again an iteration of the outer loop)
/// - but doing this requires taking a backward edge which goes to the outer loop
///
/// Whenever we exit a loop, we save the block we went to as an exit candidate
/// for this loop. Note that there may by many exit candidates. For instance,
/// in the below example:
/// ```
/// while ... {
///    ...
///    if ... {
///        // We can't reach the loop entry from here: this is an exit
///        // candidate
///        return;
///    }
/// }
/// // This is another exit candidate - and this is the one we want to use
/// // as the "real" exit...
/// ...
/// ```
///
/// Also note that it may happen that we go several times to the same exit (if
/// we use breaks for instance): we record the number of times an exit candidate
/// is used.
///
/// Once we listed all the exit candidates, we find the "best" one for every
/// loop, starting with the outer loops. We start with outer loops because
/// inner loops might use breaks to exit to the exit of outer loops: if we
/// start with the inner loops, the exit which is "natural" for the outer loop
/// might end up being used for one of the inner loops...
///
/// The best exit is the following one:
/// - it is the one which is used the most times (actually, there should be
///   at most one candidate which is referenced strictly more than once)
/// - if several exits have the same number of occurrences, we choose the one
///   for which we goto the "earliest" (earliest meaning that the goto is close to
///   the loop entry node in the AST). The reason is that all the loops should
///   have an outer if ... then ... else ... which executes the loop body or goes
///   to the exit (note that this is not necessarily the first
///   if ... then ... else ... we find: loop conditions can be arbitrary
///   expressions, containing branchings).
fn compute_loop_exits(cfg: &CfgInfo) -> HashMap<src::BlockId::Id, Option<src::BlockId::Id>> {
    let mut explored = HashSet::new();
    let mut ordered_loops = Vec::new();
    let mut loop_exits = HashMap::new();

    // Initialize the loop exits candidates
    for loop_id in &cfg.loop_entries {
        loop_exits.insert(*loop_id, LinkedHashMap::new());
    }

    // Compute the candidates
    compute_loop_exit_candidates(
        cfg,
        &mut explored,
        &mut ordered_loops,
        &mut loop_exits,
        Vector::new(),
        src::BlockId::ZERO,
    );

    {
        // Debugging
        let candidates: Vec<String> = loop_exits
            .iter()
            .map(|(loop_id, candidates)| format!("{} -> {:?}", loop_id, candidates))
            .collect();
        trace!("Loop exit candidates:\n{}", candidates.join("\n"));
    }

    // Choose one candidate among the potential candidates.
    let mut exits: HashSet<src::BlockId::Id> = HashSet::new();
    let mut chosen_loop_exits: HashMap<src::BlockId::Id, Option<src::BlockId::Id>> = HashMap::new();
    // For every loop
    for loop_id in ordered_loops {
        // Check the candidates.
        // Ignore the candidates which have already been chosen as exits for other
        // loops (which should be outer loops).
        // We choose the exit with:
        // - the most occurrences
        // - the least total distance (if there are several possibilities)

        // First:
        // - filter the candidates
        // - compute the number of occurrences
        // - compute the sum of distances
        let loop_exits = Vec::from_iter(loop_exits.get(&loop_id).unwrap().iter().filter_map(
            |(candidate_id, candidate_info)| {
                // If candidate already selected for another loop: ignore
                if exits.contains(candidate_id) {
                    None
                } else {
                    let num_occurrences = candidate_info.occurrences.len();
                    let dist_sum = candidate_info.occurrences.iter().sum();
                    Some((*candidate_id, num_occurrences, dist_sum))
                }
            },
        ));

        // Second: actually select the proper candidate.
        // We select the first one with the highest number of occurrences (we
        // take care of listing the exit candidates in a deterministic order).
        let mut best_exit: Option<src::BlockId::Id> = None;
        let mut best_occurrences = 0;
        let mut best_dist_sum = std::usize::MAX;
        for (candidate_id, occurrences, dist_sum) in loop_exits.iter() {
            if (*occurrences > best_occurrences)
                || (*occurrences == best_occurrences && *dist_sum < best_dist_sum)
            {
                best_exit = Some(*candidate_id);
                best_occurrences = *occurrences;
                best_dist_sum = *dist_sum;
            }
        }

        let num_possible_candidates = loop_exits
            .iter()
            .filter(|(_, occs, dsum)| *occs == best_occurrences && *dsum == best_dist_sum)
            .count();

        // Sanity check: there are no two different candidates with exactly the
        // same number of occurrences and dist sum if the number of occurrences
        // is 1.
        if best_occurrences > 1 {
            assert!(best_occurrences <= 1 || num_possible_candidates <= 1);
        }

        // If the best number of occurrences is 1 and there are several candidates,
        // it is actually better not to choose any.
        //
        // Example:
        // ========
        // ```
        // loop {
        //     match ls {
        //         List::Nil => {
        //             panic!() // One occurrence
        //         }
        //         List::Cons(x, tl) => {
        //             if i == 0 {
        //                 return x; // One occurrence
        //             } else {
        //                 ls = tl;
        //                 i -= 1;
        //             }
        //         }
        //     }
        // }
        // ```
        if best_occurrences == 1 && num_possible_candidates > 1 {
            // We choose not to select an exit
            chosen_loop_exits.insert(loop_id, None);
        } else {
            // Register the exit, if there is one
            match best_exit {
                None => {
                    // No exit was found
                    chosen_loop_exits.insert(loop_id, None);
                }
                Some(exit_id) => {
                    exits.insert(exit_id);
                    chosen_loop_exits.insert(loop_id, Some(exit_id));
                }
            }
        }
    }

    // Return the chosen exits
    trace!("Chosen loop exits: {:?}", chosen_loop_exits);
    chosen_loop_exits
}

/// Information used to compute the switch exits.
/// We compute this information for every block in the graph.
/// Note that we make sure to use immutable sets because we rely a lot
/// on cloning.
#[derive(Debug, Clone)]
struct BlocksInfo {
    /// All the successors of the block
    succs: im::OrdSet<OrdBlockId>,
    /// The "best" intersection between the successors of the different
    /// direct children of the block. We use this to find switch exits
    /// candidates: if the intersection is non-empty and because the
    /// elements are topologically sorted, the first block in the set
    /// should be the exit.
    /// Note that we can ignore children when computing the intersection,
    /// which is why we call it the "best" intersection. For instance, in
    /// the following:
    /// ```
    /// switch i {
    ///   0 => x = 1,
    ///   1 => x = 2,
    ///   _ => panic,
    /// }
    /// ```
    /// The branches 0 and 1 have successors which intersect, but the branch 2
    /// doesn't because it terminates: we thus ignore it.
    best_inter_succs: im::OrdSet<OrdBlockId>,
}

/// Create an [OrdBlockId] from a block id and a rank given by a map giving
/// a sort (topological in our use cases) over the graph.
fn make_ord_block_id(
    block_id: src::BlockId::Id,
    sort_map: &HashMap<src::BlockId::Id, usize>,
) -> OrdBlockId {
    let rank = *sort_map.get(&block_id).unwrap();
    OrdBlockId { id: block_id, rank }
}

/// Compute [BlocksInfo] for every block in the graph.
/// This information is then used to compute the switch exits.
fn compute_switch_exits_explore(
    cfg: &CfgInfo,
    tsort_map: &HashMap<src::BlockId::Id, usize>,
    memoized: &mut HashMap<src::BlockId::Id, BlocksInfo>,
    block_id: src::BlockId::Id,
) -> BlocksInfo {
    // Shortcut
    match memoized.get(&block_id) {
        Some(res) => {
            return res.clone();
        }
        None => (),
    }

    // Find the next blocks, and their successors
    let children: Vec<src::BlockId::Id> = Vec::from_iter(cfg.cfg_no_be.neighbors(block_id));
    let mut children_succs: Vec<im::OrdSet<OrdBlockId>> = Vec::from_iter(
        children
            .iter()
            .map(|bid| compute_switch_exits_explore(cfg, tsort_map, memoized, *bid).succs),
    );
    trace!("block: {}, children: {:?}", block_id, children);

    // Add the children themselves in their sets of successors
    for i in 0..children.len() {
        children_succs[i].insert(make_ord_block_id(children[i], tsort_map));
    }

    // Compute the full sets of successors of the children
    let all_succs: im::OrdSet<OrdBlockId> = children_succs
        .iter()
        .fold(im::OrdSet::new(), |acc, s| acc.union(s.clone()));

    // Then, compute the "best" intersection of the successors
    // If there is exactly one child or less, it is trivial
    let best_inter_succs = if children.len() <= 1 {
        all_succs.clone()
    }
    // Otherwise, there is a branching: we need to find the "best" intersection
    // of successors, which allows to factorize the code as much as possible.
    // We do it in a very "brutal" manner:
    // 1. we look for the biggest set of children such that the intersection
    //   of their successors is non empty.
    // 2. in this intersection, we take the first block id (remember we use
    //   topological sort), which will be our exit node.
    //
    // The reason behind 1 is that some branches of a match can join themselves,
    // before joining other branches. For example:
    // ```
    // let y = match x {
    //   | E1 | E2 => 0, // Those 2 branches lead to the same node
    //   | E3 => 1,
    // };
    // // But the 3 branches join this point: this is the proper exit
    // return y;
    // ```
    //
    // Note that we're definitely not looking for performance here (and that
    // there shouldn't be too many blocks in a function body), but rather
    // quality of the generated code. If the following works well but proves
    // to be too slow, we'll think of a way of making it faster.
    // Note: actually, we could look only for *any* two pair of children
    // whose successors intersection is non empty: I think it works in the
    // general case.
    else {
        let mut max_number_inter: u32 = 0;
        let mut max_inter_succs: im::OrdSet<OrdBlockId> = im::OrdSet::new();

        // For every child
        for i in 0..children_succs.len() {
            let mut current_number_inter = 1;
            // Note that we need to add the children themselves to the
            // sets of successors
            let mut i_succs = children_succs.get(i).unwrap().clone();
            i_succs.insert(make_ord_block_id(children[i], tsort_map));
            let mut current_inter_succs: im::OrdSet<OrdBlockId> = i_succs;

            // Compute the "best" intersection with all the other children
            for j in 0..children_succs.len() {
                let mut j_succs = children_succs.get(j).unwrap().clone();
                j_succs.insert(make_ord_block_id(children[j], tsort_map));

                // Annoying that we have to clone the current intersection set...
                let inter = current_inter_succs.clone().intersection(j_succs);

                if !inter.is_empty() {
                    current_number_inter += 1;
                    current_inter_succs = inter;
                }
            }

            // Update the best intersection, if necessary
            if current_number_inter > max_number_inter {
                max_number_inter = current_number_inter;
                max_inter_succs = current_inter_succs;
            }
        }

        max_inter_succs
    };

    trace!(
        "block: {}, all successors: {:?}, best intersection: {:?}",
        block_id,
        all_succs,
        best_inter_succs
    );

    // Memoize
    let info = BlocksInfo {
        succs: all_succs,
        best_inter_succs,
    };
    memoized.insert(block_id, info.clone());

    // Return
    info
}

/// See [`compute_loop_switch_exits`](compute_loop_switch_exits) for
/// explanations about what "exits" are.
///
/// In order to compute the switch exits, we simply recursively compute a
/// topologically ordered set of "filtered successors" as follows (note
/// that we work in the CFG *without* back edges):
/// - for a block which doesn't branch (only one successor), the filtered
///   successors is the set of reachable nodes.
/// - for a block which branches, we compute the nodes reachable from all
///   the children, and find the "best" intersection between those.
///   Note that we find the "best" intersection (a pair of branches which
///   maximize the intersection of filtered successors) because some branches
///   might never join the control-flow of the other branches, if they contain
///   a `break`, `return`, `panic`, etc., like here:
///   ```
///   if b { x = 3; } { return; }
///   y += x;
///   ...
///   ```
/// Note that with nested switches, the branches of the inner switches might
/// goto the exits of the outer switches: for this reason, we give precedence
/// to the outer switches.
fn compute_switch_exits(
    cfg: &CfgInfo,
    tsort_map: &HashMap<src::BlockId::Id, usize>,
) -> HashMap<src::BlockId::Id, Option<src::BlockId::Id>> {
    // Compute the successors info map, starting at the root node
    let mut succs_info_map = HashMap::new();
    let _ = compute_switch_exits_explore(cfg, tsort_map, &mut succs_info_map, src::BlockId::ZERO);

    // We need to give precedence to the outer switches: we thus iterate
    // over the switch blocks in topological order.
    let mut sorted_switch_blocks: im::OrdSet<OrdBlockId> = im::OrdSet::new();
    for bid in cfg.switch_blocks.iter() {
        sorted_switch_blocks.insert(make_ord_block_id(*bid, tsort_map));
    }

    // Debugging: print all the successors
    {
        let mut out = vec![];
        for (bid, info) in &succs_info_map {
            out.push(
                format!(
                    "{} -> {{succs: {:?}, best inter: {:?}}}",
                    bid, &info.succs, &info.best_inter_succs
                )
                .to_string(),
            );
        }
        trace!("Successors info:\n{}\n", out.join("\n"));
    }

    // For every node which is a switch, retrieve the exit.
    // As the set of intersection of successors is topologically sorted, the
    // exit should be the first node in the set (if the set is non empty).
    // Also, we need to explore the nodes in topological order, to give
    // precedence to the outer switches.
    let mut exits_set = HashSet::new();
    let mut ord_exits_set = im::OrdSet::new();
    let mut exits = HashMap::new();
    for bid in sorted_switch_blocks {
        let bid = bid.id;
        let info = succs_info_map.get(&bid).unwrap();
        let succs = &info.best_inter_succs;
        // Check if there are successors: if there are no successors shared
        // by the branches, there are no exits.
        if succs.is_empty() {
            exits.insert(bid, None);
        } else {
            // We have an exit candidate: check that it was not already
            // taken by an external switch
            let exit = succs.iter().next().unwrap();
            if exits_set.contains(&exit.id) {
                exits.insert(bid, None);
            } else {
                // It was not taken by an external switch.
                //
                // We must check that we can't reach the exit of an external
                // switch from one of the branches. We do this by simply
                // checking that we can't reach any exits (and use the fact
                // that we explore the switch by using a topological order
                // to not discard valid exit candidates).
                //
                // The reason is that it can lead to code like the following:
                // ```
                // if ... { // if #1
                //   if ... { // if #2
                //     ...
                //     // here, we have a `goto b1`, where b1 is the exit
                //     // of if #2: we thus stop translating the blocks.
                //   }
                //   else {
                //     ...
                //     // here, we have a `goto b2`, where b2 is the exit
                //     // of if #1: we thus stop translating the blocks.
                //   }
                //   // We insert code for the block b1 here (which is the exit of
                //   // the exit of if #2). However, this block should only
                //   // be executed in the branch "then" of the if #2, not in
                //   // the branch "else".
                //   ...
                // }
                // else {
                //   ...
                // }
                // ```
                let inter = info.succs.clone().intersection(ord_exits_set.clone());
                if inter.is_empty() {
                    // No intersectiàn: ok
                    exits_set.insert(exit.id);
                    ord_exits_set.insert(*exit);
                    exits.insert(bid, Some(exit.id));
                } else {
                    exits.insert(bid, None);
                }
            }
        }
    }

    exits
}

/// The exits of a graph
#[derive(Debug, Clone)]
struct ExitInfo {
    /// The loop exits
    loop_exits: HashMap<src::BlockId::Id, Option<src::BlockId::Id>>,
    /// Some loop exits actually belong to outer switches. We still need
    /// to track them in the loop exits, in order to know when we should
    /// insert a break. However, we need to make sure we don't add the
    /// corresponding block in a sequence, after having translated the
    /// loop, like so:
    /// ```
    /// loop {
    ///   loop_body
    /// };
    /// exit_blocks // OK if the exit "belongs" to the loop
    /// ```
    ///
    /// In case the exit doesn't belong to the loop:
    /// ```
    /// if b {
    ///   loop {
    ///     loop_body
    ///   } // no exit blocks after the loop
    /// }
    /// else {
    ///   ...
    /// };
    /// exit_blocks // the exit blocks are here
    /// ```
    owned_loop_exits: HashMap<src::BlockId::Id, Option<src::BlockId::Id>>,
    /// The switch exits.
    /// Note that the switch exits are always owned.
    owned_switch_exits: HashMap<src::BlockId::Id, Option<src::BlockId::Id>>,
}

/// Compute the exits for the loops and the switches (switch on integer and
/// if ... then ... else ...). We need to do this because control-flow in MIR
/// is destructured: we have gotos everywhere.
///
/// Let's consider the following piece of code:
/// ```
/// if cond1 { ... } else { ... };
/// if cond2 { ... } else { ... };
/// ```
/// Once converted to MIR, the control-flow is destructured, which means we
/// have gotos everywhere. When reconstructing the control-flow, we have
/// to be careful about the point where we should join the two branches of
/// the first if.
/// For instance, if we don't notice they should be joined at some point (i.e,
/// whatever the branch we take, there is a moment when we go to the exact
/// same place, just before the second if), we might generate code like
/// this, with some duplicata:
/// ```
/// if cond1 { ...; if cond2 { ... } else { ...} }
/// else { ...; if cond2 { ... } else { ...} }
/// ```
///
/// Such a reconstructed program is valid, but it is definitely non-optimal:
/// it is very different from the original program (making it less clean and
/// clear), more bloated, and might involve duplicating the proof effort.
///
/// For this reason, we need to find the "exit" of the first loop, which is
/// the point where the two branches join. Note that this can be a bit tricky,
/// because there may be more than two branches (if we do `switch(x) { ... }`),
/// and some of them might not join (if they contain a `break`, `panic`,
/// `return`, etc.).
///
/// Finally, some similar issues arise for loops. For instance, let's consider
/// the following piece of code:
/// ```
/// while cond1 {
///   e1;
///   if cond2 {
///     break;
///   }
///   e2;
/// }
/// e3;
/// return;
/// ```
///
/// Note that in MIR, the loop gets desugared to an if ... then ... else ....
/// From the MIR, We want to generate something like this:
/// ```
/// loop {
///   if cond1 {
///     e1;
///     if cond2 {
///       break;
///     }
///     e2;
///     continue;
///   }
///   else {
///     break;
///   }
/// };
/// e3;
/// return;
/// ```
///
/// But if we don't pay attention, we might end up with that, once again with
/// duplications:
/// ```
/// loop {
///   if cond1 {
///     e1;
///     if cond2 {
///       e3;
///       return;
///     }
///     e2;
///     continue;
///   }
///   else {
///     e3;
///     return;
///   }
/// }
/// ```
/// We thus have to notice that if the loop condition is false, we goto the same
/// block as when following the goto introduced by the break inside the loop, and
/// this block is dubbed the "loop exit".
///
/// The following function thus computes the "exits" for loops and switches, which
/// are basically the points where control-flow joins.
fn compute_loop_switch_exits(cfg_info: &CfgInfo) -> ExitInfo {
    // Use the CFG without backward edges to topologically sort the nodes.
    // Note that `toposort` returns `Err` if and only if it finds cycles (which
    // can't happen).
    let tsorted: Vec<src::BlockId::Id> = toposort(&cfg_info.cfg_no_be, None).unwrap();

    // Build the map: block id -> topological sort rank
    let tsort_map: HashMap<src::BlockId::Id, usize> = HashMap::from_iter(
        tsorted
            .into_iter()
            .enumerate()
            .map(|(i, block_id)| (block_id, i)),
    );

    // Compute the loop exits
    let loop_exits = compute_loop_exits(cfg_info);

    // Compute the switch exits
    let switch_exits = compute_switch_exits(cfg_info, &tsort_map);

    // Compute the exit info
    let mut exit_info = ExitInfo {
        loop_exits: HashMap::new(),
        owned_loop_exits: HashMap::new(),
        owned_switch_exits: HashMap::new(),
    };

    // We need to give precedence to the outer switches and loops: we thus iterate
    // over the blocks in topological order.
    let mut sorted_blocks: im::OrdSet<OrdBlockId> = im::OrdSet::new();
    for bid in cfg_info
        .loop_entries
        .iter()
        .chain(cfg_info.switch_blocks.iter())
    {
        sorted_blocks.insert(make_ord_block_id(*bid, &tsort_map));
    }

    // Keep track of the exits which were already attributed
    let mut all_exits = HashSet::new();

    // Put all this together
    for bid in sorted_blocks {
        let bid = bid.id;
        // Check if loop or switch block
        if cfg_info.loop_entries.contains(&bid) {
            // For loops, we always register the exit (if there is one).
            // However, the exit may be owned by an outer switch (note
            // that we already took care of spreading the exits between
            // the inner/outer loops)
            let exit_id = loop_exits.get(&bid).unwrap();
            exit_info.loop_exits.insert(bid, *exit_id);

            // Check if we "own" the exit
            match exit_id {
                None => {
                    // No exit
                    exit_info.owned_loop_exits.insert(bid, None);
                }
                Some(exit_id) => {
                    if all_exits.contains(exit_id) {
                        // We don't own it
                        exit_info.owned_loop_exits.insert(bid, None);
                    } else {
                        // We own it
                        exit_info.owned_loop_exits.insert(bid, Some(*exit_id));
                        all_exits.insert(*exit_id);
                    }
                }
            }
        } else {
            // For switches: check that the exit was not already given to a
            // loop
            let exit_id = switch_exits.get(&bid).unwrap();

            match exit_id {
                None => {
                    // No exit
                    exit_info.owned_switch_exits.insert(bid, None);
                }
                Some(exit_id) => {
                    if all_exits.contains(exit_id) {
                        // We don't own it
                        exit_info.owned_switch_exits.insert(bid, None);
                    } else {
                        // We own it
                        exit_info.owned_switch_exits.insert(bid, Some(*exit_id));
                        all_exits.insert(*exit_id);
                    }
                }
            }
        }
    }

    exit_info
}

fn combine_statement_and_statement(
    statement: tgt::Statement,
    next_st: Option<tgt::Statement>,
) -> tgt::Statement {
    match next_st {
        Some(next_st) => tgt::Statement::Sequence(Box::new(statement), Box::new(next_st)),
        None => statement,
    }
}

fn combine_statements_and_statement(
    statements: Vec<tgt::Statement>,
    next: Option<tgt::Statement>,
) -> Option<tgt::Statement> {
    statements.into_iter().rev().fold(next, |seq, st| {
        Some(combine_statement_and_statement(st, seq))
    })
}

fn get_goto_kind(
    exits_info: &ExitInfo,
    parent_loops: &Vector<src::BlockId::Id>,
    switch_exit_blocks: &im::HashSet<src::BlockId::Id>,
    next_block_id: src::BlockId::Id,
) -> GotoKind {
    // First explore the parent loops in revert order
    let len = parent_loops.len();
    for i in 0..len {
        let loop_id = parent_loops.get(len - i - 1).unwrap();

        // If we goto a loop entry node: this is a 'continue'
        if next_block_id == *loop_id {
            return GotoKind::Continue(i);
        } else {
            // If we goto a loop exit node: this is a 'break'
            match exits_info.loop_exits.get(&loop_id).unwrap() {
                None => (),
                Some(exit_id) => {
                    if *exit_id == next_block_id {
                        return GotoKind::Break(i);
                    }
                }
            }
        }
    }

    // Check if the goto exits the current block
    if switch_exit_blocks.contains(&next_block_id) {
        return GotoKind::ExitBlock;
    }

    // Default
    return GotoKind::Goto;
}

enum GotoKind {
    Break(usize),
    Continue(usize),
    ExitBlock,
    Goto,
}

fn translate_child_block(
    no_code_duplication: bool,
    cfg: &CfgInfo,
    body: &src::ExprBody,
    exits_info: &ExitInfo,
    parent_loops: Vector<src::BlockId::Id>,
    switch_exit_blocks: &im::HashSet<src::BlockId::Id>,
    explored: &mut HashSet<src::BlockId::Id>,
    child_id: src::BlockId::Id,
) -> Option<tgt::Statement> {
    // Check if this is a backward call
    match get_goto_kind(exits_info, &parent_loops, switch_exit_blocks, child_id) {
        GotoKind::Break(index) => Some(tgt::Statement::Break(index)),
        GotoKind::Continue(index) => Some(tgt::Statement::Continue(index)),
        // If we are going to an exit block we simply ignore the goto
        GotoKind::ExitBlock => None,
        GotoKind::Goto => {
            // "Standard" goto: just recursively translate
            translate_block(
                no_code_duplication,
                cfg,
                body,
                exits_info,
                parent_loops,
                switch_exit_blocks,
                explored,
                child_id,
            )
        }
    }
}

fn opt_statement_to_nop_if_none(opt_st: Option<tgt::Statement>) -> tgt::Statement {
    match opt_st {
        Some(st) => st,
        None => tgt::Statement::Nop,
    }
}

fn translate_statement(st: &src::Statement) -> Option<tgt::Statement> {
    match st {
        src::Statement::Assign(place, rvalue) => {
            Some(tgt::Statement::Assign(place.clone(), rvalue.clone()))
        }
        src::Statement::FakeRead(place) => Some(tgt::Statement::FakeRead(place.clone())),
        src::Statement::SetDiscriminant(place, variant_id) => {
            Some(tgt::Statement::SetDiscriminant(place.clone(), *variant_id))
        }
        src::Statement::StorageDead(_var_id) => None,
    }
}

fn translate_terminator(
    no_code_duplication: bool,
    cfg: &CfgInfo,
    body: &src::ExprBody,
    exits_info: &ExitInfo,
    parent_loops: Vector<src::BlockId::Id>,
    switch_exit_blocks: &im::HashSet<src::BlockId::Id>,
    explored: &mut HashSet<src::BlockId::Id>,
    terminator: &src::Terminator,
) -> Option<tgt::Statement> {
    match terminator {
        src::Terminator::Panic | src::Terminator::Unreachable => Some(tgt::Statement::Panic),
        src::Terminator::Return => Some(tgt::Statement::Return),
        src::Terminator::Goto { target } => translate_child_block(
            no_code_duplication,
            cfg,
            body,
            exits_info,
            parent_loops,
            switch_exit_blocks,
            explored,
            *target,
        ),
        src::Terminator::Drop { place, target } => {
            let opt_child = translate_child_block(
                no_code_duplication,
                cfg,
                body,
                exits_info,
                parent_loops,
                switch_exit_blocks,
                explored,
                *target,
            );
            let st = tgt::Statement::Drop(place.clone());
            Some(combine_statement_and_statement(st, opt_child))
        }
        src::Terminator::Call {
            func,
            region_args,
            type_args,
            args,
            dest,
            target,
        } => {
            let opt_child = translate_child_block(
                no_code_duplication,
                cfg,
                body,
                exits_info,
                parent_loops,
                switch_exit_blocks,
                explored,
                *target,
            );
            let st = tgt::Statement::Call(tgt::Call {
                func: func.clone(),
                region_args: region_args.clone(),
                type_args: type_args.clone(),
                args: args.clone(),
                dest: dest.clone(),
            });
            Some(combine_statement_and_statement(st, opt_child))
        }
        src::Terminator::Assert {
            cond,
            expected,
            target,
        } => {
            let opt_child = translate_child_block(
                no_code_duplication,
                cfg,
                body,
                exits_info,
                parent_loops,
                switch_exit_blocks,
                explored,
                *target,
            );
            let st = tgt::Statement::Assert(tgt::Assert {
                cond: cond.clone(),
                expected: *expected,
            });
            Some(combine_statement_and_statement(st, opt_child))
        }
        src::Terminator::Switch { discr, targets } => {
            // Translate the target expressions
            let targets = match &targets {
                src::SwitchTargets::If(then_tgt, else_tgt) => {
                    // Translate the children expressions
                    let then_exp = translate_child_block(
                        no_code_duplication,
                        cfg,
                        body,
                        exits_info,
                        parent_loops.clone(),
                        switch_exit_blocks,
                        explored,
                        *then_tgt,
                    );
                    let then_exp = opt_statement_to_nop_if_none(then_exp);
                    let else_exp = translate_child_block(
                        no_code_duplication,
                        cfg,
                        body,
                        exits_info,
                        parent_loops.clone(),
                        switch_exit_blocks,
                        explored,
                        *else_tgt,
                    );
                    let else_exp = opt_statement_to_nop_if_none(else_exp);

                    // Translate
                    tgt::SwitchTargets::If(Box::new(then_exp), Box::new(else_exp))
                }
                src::SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                    // Note that some branches can be grouped together, like
                    // here:
                    // ```
                    // match e {
                    //   E::V1 | E::V2 => ..., // Grouped
                    //   E::V3 => ...
                    // }
                    // ```
                    // We detect this by checking if a block has already been
                    // translated as one of the branches of the switch.
                    //
                    // Rk.: note there may be intermediate gotos depending
                    // on the MIR we use. Typically, we manage to detect the
                    // grouped branches with Optimized MIR, but not with Promoted
                    // MIR. See the comment in "tests/src/matches.rs".

                    // We link block ids to:
                    // - vector of matched integer values
                    // - translated blocks
                    let mut branches: LinkedHashMap<
                        src::BlockId::Id,
                        (Vec<v::ScalarValue>, tgt::Statement),
                    > = LinkedHashMap::new();

                    // Translate the children expressions
                    for (v, bid) in targets.iter() {
                        // Check if the block has already been translated:
                        // if yes, it means we need to group branches
                        if branches.contains_key(bid) {
                            // Already translated: add the matched value to
                            // the list of values
                            let branch = branches.get_mut(bid).unwrap();
                            branch.0.push(*v);
                        } else {
                            // Not translated: translate it
                            let exp = translate_child_block(
                                no_code_duplication,
                                cfg,
                                body,
                                exits_info,
                                parent_loops.clone(),
                                switch_exit_blocks,
                                explored,
                                *bid,
                            );
                            let exp = opt_statement_to_nop_if_none(exp);
                            branches.insert(*bid, (vec![*v], exp));
                        }
                    }
                    let targets_exps: Vec<(Vec<v::ScalarValue>, tgt::Statement)> =
                        branches.into_iter().map(|(_, x)| x).collect();

                    let otherwise_exp = translate_child_block(
                        no_code_duplication,
                        cfg,
                        body,
                        exits_info,
                        parent_loops.clone(),
                        switch_exit_blocks,
                        explored,
                        *otherwise,
                    );
                    let otherwise_exp = opt_statement_to_nop_if_none(otherwise_exp);

                    // Translate
                    tgt::SwitchTargets::SwitchInt(*int_ty, targets_exps, Box::new(otherwise_exp))
                }
            };

            // Return
            Some(tgt::Statement::Switch(discr.clone(), targets))
        }
    }
}

fn combine_expressions(
    exp1: Option<tgt::Statement>,
    exp2: Option<tgt::Statement>,
) -> Option<tgt::Statement> {
    match exp1 {
        None => exp2,
        Some(exp1) => match exp2 {
            None => Some(exp1),
            Some(exp2) => Some(tgt::Statement::Sequence(Box::new(exp1), Box::new(exp2))),
        },
    }
}

fn is_terminal(exp: &tgt::Statement) -> bool {
    is_terminal_explore(0, exp)
}

/// Return `true` if whatever the path we take, evaluating the statement
/// necessarily leads to:
/// - a panic or return
/// - a break which goes to a loop outside the expression
/// - a continue statement
fn is_terminal_explore(num_loops: usize, st: &tgt::Statement) -> bool {
    match st {
        tgt::Statement::Assign(_, _)
        | tgt::Statement::AssignGlobal(_, _)
        | tgt::Statement::FakeRead(_)
        | tgt::Statement::SetDiscriminant(_, _)
        | tgt::Statement::Drop(_)
        | tgt::Statement::Assert(_)
        | tgt::Statement::Call(_)
        | tgt::Statement::Nop => false,
        tgt::Statement::Panic | tgt::Statement::Return => true,
        tgt::Statement::Break(index) => *index >= num_loops,
        tgt::Statement::Continue(_index) => true,
        tgt::Statement::Sequence(st1, st2) => {
            if is_terminal_explore(num_loops, st1) {
                return true;
            } else {
                return is_terminal_explore(num_loops, st2);
            }
        }
        tgt::Statement::Switch(_, targets) => targets
            .get_targets()
            .iter()
            .all(|tgt_st| is_terminal_explore(num_loops, tgt_st)),
        tgt::Statement::Loop(loop_st) => {
            return is_terminal_explore(num_loops + 1, loop_st);
        }
    }
}

fn translate_block(
    no_code_duplication: bool,
    cfg: &CfgInfo,
    body: &src::ExprBody,
    exits_info: &ExitInfo,
    parent_loops: Vector<src::BlockId::Id>,
    switch_exit_blocks: &im::HashSet<src::BlockId::Id>,
    explored: &mut HashSet<src::BlockId::Id>,
    block_id: src::BlockId::Id,
) -> Option<tgt::Statement> {
    // If the user activated this check: check that we didn't already translate
    // this block, and insert the block id in the set of already translated blocks.
    trace!(
        "Parent loops: {:?}, Parent switch exits: {:?}, Block id: {}",
        parent_loops,
        switch_exit_blocks,
        block_id
    );
    if no_code_duplication {
        assert!(!explored.contains(&block_id));
    }
    explored.insert(block_id);

    let block = body.body.get(block_id).unwrap();

    // Check if we enter a loop: if so, update parent_loops and the current_exit_block
    let is_loop = cfg.loop_entries.contains(&block_id);
    let nparent_loops = if cfg.loop_entries.contains(&block_id) {
        let mut nparent_loops = parent_loops.clone();
        nparent_loops.push_back(block_id);
        nparent_loops
    } else {
        parent_loops.clone()
    };

    // If we enter a switch or a loop, we need to check if we own the exit
    // block, in which case we need to append it to the loop/switch body
    // in a sequence
    let is_switch = block.terminator.is_switch();
    let next_block = if is_loop {
        *exits_info.owned_loop_exits.get(&block_id).unwrap()
    } else if is_switch {
        *exits_info.owned_switch_exits.get(&block_id).unwrap()
    } else {
        Option::None
    };

    // If we enter a switch, add the exit block to the set
    // of outer exit blocks
    let nswitch_exit_blocks = if is_switch {
        let mut nexit_blocks = switch_exit_blocks.clone();
        match next_block {
            Option::None => nexit_blocks,
            Option::Some(bid) => {
                nexit_blocks.insert(bid);
                nexit_blocks
            }
        }
    } else {
        switch_exit_blocks.clone()
    };

    // Translate the terminator and the subsequent blocks.
    // Note that this terminator is an option: we might ignore it
    // (if it is an exit).
    let terminator = translate_terminator(
        no_code_duplication,
        cfg,
        body,
        exits_info,
        nparent_loops,
        &nswitch_exit_blocks,
        explored,
        &block.terminator,
    );

    // Translate the statements inside the block
    let statements = Vec::from_iter(
        block
            .statements
            .iter()
            .filter_map(|st| translate_statement(st)),
    );

    // We do different things if this is a loop, a switch (which is not
    // a loop) or something else.
    // Note that we need to do different treatments, because we don't
    // concatenate the exit block the same way for loops and switches.
    // In particular, for switches, we have to make sure we concatenate
    // the exit block *before* concatenating the statements preceding
    // the terminator, in order to avoid generating code of the form:
    // ```
    // e_prev; (s1; ...: sn; switch ...); e_switch_exit
    // ```
    if is_loop {
        // Put the statements and the terminator together
        let exp = combine_statements_and_statement(statements, terminator);

        // Put the whole loop body inside a `Loop` wrapper
        let exp = tgt::Statement::Loop(Box::new(exp.unwrap()));

        // Add the exit block
        let exp = if next_block.is_some() {
            let exit_block_id = next_block.unwrap();
            let next_exp = translate_block(
                no_code_duplication,
                cfg,
                body,
                exits_info,
                parent_loops,
                switch_exit_blocks,
                explored,
                exit_block_id,
            );
            combine_expressions(Some(exp), next_exp)
        } else {
            Some(exp)
        };

        exp
    } else if is_switch {
        // Use the terminator
        let exp = terminator.unwrap();

        // Concatenate the exit expression, if needs be
        let exp = if next_block.is_some() {
            // Sanity check: if there is an exit block, this block must be
            // reachable (i.e, there must exist a path in the switch which
            // doesn't end with `panic`, `return`, etc.).
            assert!(!is_terminal(&exp));

            let exit_block_id = next_block.unwrap();
            let next_exp = translate_block(
                no_code_duplication,
                cfg,
                body,
                exits_info,
                parent_loops,
                switch_exit_blocks,
                explored,
                exit_block_id,
            );
            combine_expressions(Some(exp), next_exp)
        } else {
            Some(exp)
        };

        // Concatenate the statements
        combine_statements_and_statement(statements, exp)
    } else {
        // Simply concatenate the statements and the terminator
        combine_statements_and_statement(statements, terminator)
    }
}

/// [type_defs]: this parameter is used for pretty-printing purposes
fn translate_body(no_code_duplication: bool, src_body: &src::ExprBody) -> tgt::ExprBody {
    // Explore the function body to create the control-flow graph without backward
    // edges, and identify the loop entries (which are destinations of backward edges).
    let cfg_info = build_cfg_partial_info(src_body);
    let cfg_info = compute_cfg_info_from_partial(cfg_info);

    // Find the exit block for all the loops and switches, if such an exit point
    // exists.
    let exits_info = compute_loop_switch_exits(&cfg_info);

    // Debugging
    trace!("exits map:\n{:?}", exits_info);

    // Translate the body by reconstructing the loops and the
    // conditional branchings.
    // Note that we shouldn't get `None`.
    let mut explored = HashSet::new();
    let stmt = translate_block(
        no_code_duplication,
        &cfg_info,
        src_body,
        &exits_info,
        Vector::new(),
        &im::HashSet::new(),
        &mut explored,
        src::BlockId::ZERO,
    )
    .unwrap();

    // Sanity: check that we translated all the blocks
    for (bid, _) in src_body.body.iter_indexed_values() {
        assert!(explored.contains(&bid));
    }

    tgt::ExprBody {
        arg_count: src_body.arg_count,
        locals: src_body.locals.clone(),
        body: stmt,
    }
}

/// [type_defs] [global_defs]: this parameter is used for pretty-printing purposes
fn translate_function(
    no_code_duplication: bool,
    type_defs: &TypeDecls,
    src_defs: &src::FunDecls,
    src_def_id: FunDeclId::Id,
    global_defs: &src::GlobalDecls,
) -> tgt::FunDecl {
    // Retrieve the function definition
    let src_def = src_defs.get(src_def_id).unwrap();
    trace!(
        "# Reconstructing: {}\n\n{}",
        src_def.name,
        src_def.fmt_with_defs(&type_defs, &src_defs, &global_defs)
    );

    // Return the translated definition
    tgt::FunDecl {
        def_id: src_def.def_id,
        name: src_def.name.clone(),
        signature: src_def.signature.clone(),
        body: src_def
            .body
            .as_ref()
            .map(|b| translate_body(no_code_duplication, b)),
    }
}

fn translate_global(
    no_code_duplication: bool,
    type_defs: &TypeDecls,
    global_defs: &src::GlobalDecls,
    global_id: GlobalDeclId::Id,
    fun_defs: &src::FunDecls,
) -> tgt::GlobalDecl {
    // Retrieve the global definition
    let src_def = global_defs.get(global_id).unwrap();
    trace!(
        "# Reconstructing: {}\n\n{}",
        src_def.name,
        src_def.fmt_with_defs(&type_defs, &fun_defs, &global_defs)
    );

    tgt::GlobalDecl {
        def_id: src_def.def_id,
        name: src_def.name.clone(),
        ty: src_def.ty.clone(),
        body: src_def
            .body
            .as_ref()
            .map(|b| translate_body(no_code_duplication, b)),
    }
}

/// Translate the functions by reconstructing the control-flow.
///
/// [no_code_duplication]: if true, check that no block is translated twice (this
/// can be a sign that the reconstruction is of poor quality, but sometimes
/// code duplication is necessary, in the presence of "fused" match branches for
/// instance).
pub fn translate_functions(
    no_code_duplication: bool,
    type_defs: &TypeDecls,
    src_funs: &src::FunDecls,
    src_globals: &src::GlobalDecls,
) -> Defs {
    let mut tgt_funs = FunDeclId::Vector::new();
    let mut tgt_globals = GlobalDeclId::Vector::new();

    // Translate the bodies one at a time
    for fun_id in src_funs.iter_indices() {
        tgt_funs.push_back(translate_function(
            no_code_duplication,
            type_defs,
            src_funs,
            fun_id,
            src_globals,
        ));
    }
    for global_id in src_globals.iter_indices() {
        tgt_globals.push_back(translate_global(
            no_code_duplication,
            type_defs,
            src_globals,
            global_id,
            src_funs,
        ));
    }

    // Print the functions
    for fun in &tgt_funs {
        trace!(
            "# Signature:\n{}\n\n# Function definition:\n{}\n",
            fun.signature.fmt_with_defs(&type_defs),
            fun.fmt_with_defs(&type_defs, &tgt_funs, &tgt_globals)
        );
    }
    // Print the global variables
    for global in &tgt_globals {
        trace!(
            "# Type:\n{:?}\n\n# Global definition:\n{}\n",
            global.ty,
            global.fmt_with_defs(&type_defs, &tgt_funs, &tgt_globals)
        );
    }

    (tgt_funs, tgt_globals)
}
