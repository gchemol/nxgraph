// mods

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*mods][mods:1]]
mod graph;
// mods:1 ends here

// pub

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*pub][pub:1]]
pub use crate::graph::*;

// re-exports for adhoc uses
#[cfg(feature = "adhoc")]
pub use petgraph;
// pub:1 ends here
