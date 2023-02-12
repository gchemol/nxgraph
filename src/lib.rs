// [[file:../nxgraph.note::*docs][docs:1]]
//! NxGraph: A networkx-like API wrapper around petgraph for chemistry.
// docs:1 ends here

// [[file:../nxgraph.note::*mods][mods:1]]
// #![deny(missing_docs)] // rustdoc will fail if there is missing docs

#[cfg(feature = "adhoc")]
mod algo;
mod graph;
// mods:1 ends here

// [[file:../nxgraph.note::195f6547][195f6547]]
pub use crate::graph::*;

// re-exports for adhoc uses
#[cfg(feature = "adhoc")]
pub use petgraph;
// 195f6547 ends here
