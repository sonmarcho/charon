//! Tests with constants
#![allow(dead_code)]

// Integers

const X0: u32 = 0;

const X1: u32 = u32::MAX;

const X2: u32 = {
    let x = 3;
    x
};

const X3: u32 = incr(32);

const fn incr(n: u32) -> u32 {
    n + 1
}

// Pairs

const fn mk_pair0(x: u32, y: u32) -> (u32, u32) {
    (x, y)
}

const fn mk_pair1(x: u32, y: u32) -> Pair<u32, u32> {
    Pair { x, y }
}

const P0: (u32, u32) = mk_pair0(0, 1);
const P1: Pair<u32, u32> = mk_pair1(0, 1);
const P2: (u32, u32) = (0, 1);
const P3: Pair<u32, u32> = Pair { x: 0, y: 1 };

pub struct Pair<T1, T2> {
    x: T1,
    y: T2,
}

const Y: Wrap<i32> = Wrap::new(2);

const fn unwrap_y() -> i32 {
    Y.val
}

const YVAL: i32 = unwrap_y();

struct Wrap<T> {
    val: T,
}

impl<T> Wrap<T> {
    const fn new(val: T) -> Wrap<T> {
        Wrap { val }
    }
}

// Additions

const fn get_z1() -> i32 {
    const Z1: i32 = 3;
    Z1
}

const fn add(a: i32, b: i32) -> i32 {
    a + b
}

const fn get_z2() -> i32 {
    add(Q1, add(get_z1(), Q3))
}

const Q1: i32 = 5;
const Q2: i32 = Q1;
const Q3: i32 = add(Q2, 3);

// Statiques

static S1: u32 = 6;
static S2: u32 = incr(S1);
static S3: Pair<u32, u32> = P3;
static S4: Pair<u32, u32> = mk_pair1(7, 8);
