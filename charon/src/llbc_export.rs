use crate::common::*;
use crate::im_ast::FunDeclId;
use crate::im_ast::GlobalDeclId;
use crate::llbc_ast::*;
use crate::rust_to_local_ids::*;
use crate::types::*;
use serde::{Serialize, Serializer};
use std::fs::File;
use std::path::PathBuf;

/// Serialization wrapper for vectors
pub struct VecSW<'a, T> {
    pub vector: &'a Vec<T>,
}

impl<'a, T> VecSW<'a, T> {
    pub fn new(vector: &'a Vec<T>) -> Self {
        VecSW { vector }
    }
}

impl<'a, T: Serialize> Serialize for VecSW<'a, T> {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serialize_vec(self.vector, serializer)
    }
}

/// An auxiliary type used for serialization of declaration groups
type DeclarationsSerializer<'a> = VecSW<'a, DeclarationGroup>;

#[derive(Serialize)]
#[serde(rename = "Module")]
struct ModSerializer<'a> {
    name: String,
    declarations: DeclarationsSerializer<'a>,
    types: &'a TypeDeclId::Vector<TypeDecl>,
    functions: &'a FunDeclId::Vector<FunDecl>,
    globals: &'a GlobalDeclId::Vector<GlobalDecl>,
}

/// Export the translated definitions to a JSON file.
pub fn export(
    name: String,
    ordered_decls: &OrderedDecls,
    type_defs: &TypeDecls,
    fun_defs: &FunDecls,
    global_defs: &GlobalDecls,
    dest_dir: &Option<PathBuf>,
    sourcefile: &PathBuf,
) -> Result<()> {
    // Generate the destination file
    let target_filename = match dest_dir {
        None => {
            // No destination directory: we just need to update the file extension
            let mut tgt = sourcefile.clone();
            assert!(tgt.set_extension("llbc"));
            tgt
        }
        Some(dest_dir) => {
            // There is a destination directory
            let mut tgt = dest_dir.clone();

            // Retrieve the file name (without the source directory)
            let filename = sourcefile.file_name().unwrap();

            // Put together, and change the extension
            tgt.push(filename);
            assert!(tgt.set_extension("llbc"));
            tgt
        }
    };

    trace!("Target file: {:?}", target_filename);

    // Serialize
    let mod_serializer = ModSerializer {
        name,
        declarations: VecSW::new(&ordered_decls.decls),
        types: &type_defs.types,
        functions: &fun_defs,
        globals: &global_defs,
    };

    // Create the directory, if necessary (note that if the target directory
    // is not specified, there is no need to create it: otherwise we
    // couldn't have read the input file in the first place).
    match dest_dir {
        Option::None => (),
        Option::Some(dest_dir) => match std::fs::create_dir_all(dest_dir) {
            std::result::Result::Ok(()) => (),
            std::result::Result::Err(_) => {
                error!("Could not create the directory: {:?}", dest_dir);
                return Err(());
            }
        },
    };

    // Write to the file
    match File::create(target_filename.clone()) {
        std::io::Result::Ok(outfile) => match serde_json::to_writer(&outfile, &mod_serializer) {
            std::result::Result::Ok(()) => Ok(()),
            std::result::Result::Err(_) => {
                error!("Could not write to: {:?}", target_filename);
                Err(())
            }
        },
        std::io::Result::Err(_) => {
            error!("Could not open: {:?}", target_filename);
            Err(())
        }
    }
}
