// docs

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*docs][docs:1]]
//! NxGraph: A networkx-like API wrapper around petgraph for chemistry.
// docs:1 ends here

// mods

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*mods][mods:1]]
// #![deny(missing_docs)] // rustdoc will fail if there is missing docs

#[cfg(feature = "adhoc")]
mod algo;
mod graph;
// mods:1 ends here

// pub

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*pub][pub:1]]
pub use crate::graph::*;

// re-exports for adhoc uses
#[cfg(feature = "adhoc")]
pub use petgraph;
// pub:1 ends here
