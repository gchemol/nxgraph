// [[file:../nxgraph.note::*imports][imports:1]]
use crate::graph::{NodeIndex, NxGraph};

use itertools::Itertools;
// imports:1 ends here

// [[file:../nxgraph.note::d40009e1][d40009e1]]
/// Graph algorithms
impl<N, E> NxGraph<N, E>
where
    N: Default + Clone,
    E: Default + Clone,
{
    /// Returns an iterator over subgraphs induced by connected components in
    /// arbitrary order.
    pub fn connected_components(&self) -> impl Iterator<Item = Self> + '_ {
        // get fragments from connected components
        let components = petgraph::algo::kosaraju_scc(self.raw_graph());
        components.into_iter().map(move |nodes| self.subgraph(&nodes))
    }

    /// Returns the number of connected components.
    pub fn n_connected_components(&self) -> usize {
        let n = self.number_of_nodes();
        if n <= 1 {
            n
        } else {
            // need petgraph::Graph without without NodeIndex holes
            let graph = petgraph::Graph::from(self.raw_graph().clone());
            petgraph::algo::connected_components(&graph)
        }
    }

    /// Returns a subgraph induced on `nodes`. The induced subgraph of
    /// the graph contains the nodes in `nodes` in the same order and
    /// the edges between those nodes.
    ///
    /// # Example
    ///
    /// ```
    /// use gchemol_graph::NxGraph;
    /// 
    /// // g: 1--2--3--4
    /// let mut g = NxGraph::path_graph(4);
    /// let nodes: Vec<_> = g.node_indices().collect();
    /// 
    /// // g: 1--2--3
    /// let h = g.subgraph(&nodes[0..3]);
    /// assert_eq!(h.number_of_nodes(), 3);
    /// assert_eq!(h.number_of_edges(), 2);
    /// ```
    ///
    /// # Panic
    ///
    /// * panics if there is any duplicate in `nodes`
    ///
    /// # Reference
    ///
    /// * https://networkx.github.io/documentation/stable/reference/classes/generated/networkx.Graph.subgraph.html
    pub fn subgraph(&self, nodes: &[NodeIndex]) -> Self {
        use std::collections::{HashMap, HashSet};

        // sanity check
        let nodes_set: HashSet<_> = nodes.iter().copied().collect();
        assert_eq!(nodes_set.len(), nodes.len(), "nodes have duplicate {nodes:?}");

        let edges_ = self.edges();
        let nodes_ = self.nodes();
        let mut subgraph = Self::new();
        // add nodes
        // mapping old node index => new node index
        let map: HashMap<_, _> = nodes
            .iter()
            .map(|&n| {
                let n_new = subgraph.add_node(nodes_[n].clone());
                (n, n_new)
            })
            .collect();

        // add edges
        for &i in nodes {
            for j in self.neighbors(i) {
                if j > i && nodes.contains(&j) {
                    let eij = edges_[(i, j)].clone();
                    subgraph.add_edge(map[&i], map[&j], eij);
                }
            }
        }

        subgraph

        // NOTE: the follow codes simply works, but the node order of
        // resulted graph is different from `nodes`

        // let mut subgraph = self.raw_graph().clone();
        // subgraph.retain_nodes(|_, n| nodes_set.contains(&n));

        // Self::from_raw_graph(subgraph)
    }
}
// d40009e1 ends here

// [[file:../nxgraph.note::98add588][98add588]]
#[test]
fn test_subgraph() {
    // subgraph
    // g: 1--2--3--4
    let mut g = NxGraph::path_graph(4);
    let nodes: Vec<_> = g.node_indices().collect();
    let h = g.subgraph(&[nodes[1], nodes[0], nodes[2]]);
    assert_eq!(h.number_of_nodes(), 3);
    assert_eq!(h.number_of_edges(), 2);
    // subgraph should maintain the node orders
    assert_eq!(h.nodes().map(|(_, &n)| n).collect_vec(), vec![2, 1, 3]);

    // subgraphs from connected components
    // g: 1--2--3--4 10--11--12
    let nodes = g.add_nodes_from(vec![10, 11, 12]);
    g.add_edges_from(vec![(nodes[0], nodes[1], 1), (nodes[1], nodes[2], 1)]);
    let mut gs: Vec<_> = g.connected_components().collect();
    assert_eq!(gs.len(), 2);
    assert_eq!(gs.len(), g.n_connected_components());

    gs.sort_by_key(|x| x.number_of_nodes());
    let nodes_data_a: Vec<_> = gs[0].nodes().map(|(_, n)| *n).collect();
    let nodes_data_b: Vec<_> = gs[1].nodes().map(|(_, n)| *n).collect();

    assert_eq!(nodes_data_a, vec![10, 11, 12]);
    assert_eq!(nodes_data_b, vec![1, 2, 3, 4]);
}
// 98add588 ends here
