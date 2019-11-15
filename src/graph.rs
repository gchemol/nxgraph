// imports

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*imports][imports:1]]
use std::collections::HashMap;

use petgraph::prelude::*;

use guts::prelude::*;
// imports:1 ends here

// exports

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*exports][exports:1]]
pub use petgraph::prelude::NodeIndex;
// exports:1 ends here

// core

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*core][core:1]]
#[derive(Clone, Debug, Default)]
/// networkx-like API wrapper around petgraph
pub struct NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    mapping: HashMap<(NodeIndex, NodeIndex), EdgeIndex>,
    graph: StableUnGraph<N, E>,
}

/// return sorted node pair as mapping key.
fn node_pair_key(n1: NodeIndex, n2: NodeIndex) -> (NodeIndex, NodeIndex) {
    if n1 > n2 {
        (n2, n1)
    } else {
        (n1, n2)
    }
}

impl<N, E> NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    pub fn new() -> Self {
        Self {
            ..Default::default()
        }
    }

    fn edge_index_between(&self, n1: NodeIndex, n2: NodeIndex) -> Option<EdgeIndex> {
        // this is slow
        // self.graph.find_edge(n1, n2)

        // make sure n1 is always smaller than n2.
        let (n1, n2) = if n1 > n2 { (n2, n1) } else { (n1, n2) };

        self.mapping.get(&node_pair_key(n1, n2)).map(|v| *v)
    }

    /// Return data associated with node `n`.
    fn get_node_data(&self, n: NodeIndex) -> &N {
        self.graph.node_weight(n).expect("no node")
    }

    /// Return a mutable reference of data associated with node `n`.
    fn get_node_data_mut(&mut self, n: NodeIndex) -> &mut N {
        self.graph.node_weight_mut(n).expect("no node")
    }

    /// Return data associated with edge `node1--node2`.
    fn get_edge_data(&self, node1: NodeIndex, node2: NodeIndex) -> &E {
        let edge_index = self
            .edge_index_between(node1, node2)
            .expect("no edge index");
        self.graph.edge_weight(edge_index).expect("no edge")
    }

    /// Return a mutable reference of data associated with edge `node1--node2`.
    fn get_edge_data_mut(&mut self, node1: NodeIndex, node2: NodeIndex) -> &mut E {
        let edge_index = self
            .edge_index_between(node1, node2)
            .expect("no edge index");
        self.graph.edge_weight_mut(edge_index).expect("no edge")
    }
}
// core:1 ends here

// base

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*base][base:1]]
impl<N, E> NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    /// Return neighboring nodes of `current` node.
    pub fn neighbors(&self, current: NodeIndex) -> impl Iterator<Item = NodeIndex> + '_ {
        self.graph.neighbors(current)
    }

    /// Returns true if the graph contains the node n.
    ///
    /// Parameters
    /// ----------
    /// n : node
    pub fn has_node(&self, n: NodeIndex) -> bool {
        self.graph.contains_node(n)
    }

    /// Returns true if the edge (u, v) is in the graph.
    pub fn has_edge(&self, u: NodeIndex, v: NodeIndex) -> bool {
        self.graph.find_edge(u, v).is_some()
    }

    /// Returns the number of nodes in the graph.
    pub fn number_of_nodes(&self) -> usize {
        self.graph.node_count()
    }

    /// Returns the number of edges in the graph.
    pub fn number_of_edges(&self) -> usize {
        self.graph.edge_count()
    }
}
// base:1 ends here

// edit

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*edit][edit:1]]
impl<N, E> NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    /// Add a node with associated data into graph.
    pub fn add_node(&mut self, data: N) -> NodeIndex {
        self.graph.add_node(data)
    }

    /// Add an edge with `data` between `u` and `v`.
    pub fn add_edge(&mut self, u: NodeIndex, v: NodeIndex, data: E) {
        let e = self.graph.add_edge(u, v, data);

        // update node pair to edge index mapping.
        self.mapping.insert(node_pair_key(u, v), e);
    }

    /// Remove an edge between `node1` and `node2`. Attempting to remove a
    /// non-existent edge will cause panic.
    pub fn remove_edge(&mut self, node1: NodeIndex, node2: NodeIndex) {
        let e = self
            .mapping
            .remove(&node_pair_key(node1, node2))
            .expect("no edge");

        self.graph.remove_edge(e);
    }

    /// Removes the node `n` and all adjacent edges. Attempting to remove a
    /// non-existent node will cause panic.
    pub fn remove_node(&mut self, n: NodeIndex) {
        let _ = self.graph.remove_node(n);
    }
}
// edit:1 ends here

// node

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*node][node:1]]
impl<N, E> std::ops::Index<NodeIndex> for NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    type Output = N;

    fn index(&self, n: NodeIndex) -> &Self::Output {
        self.get_node_data(n)
    }
}

impl<N, E> std::ops::IndexMut<NodeIndex> for NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    fn index_mut(&mut self, n: NodeIndex) -> &mut Self::Output {
        self.get_node_data_mut(n)
    }
}
// node:1 ends here

// edge

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*edge][edge:1]]
impl<N, E> std::ops::Index<(NodeIndex, NodeIndex)> for NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    type Output = E;

    fn index(&self, e: (NodeIndex, NodeIndex)) -> &Self::Output {
        self.get_edge_data(e.0, e.1)
    }
}

impl<N, E> std::ops::IndexMut<(NodeIndex, NodeIndex)> for NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    fn index_mut(&mut self, e: (NodeIndex, NodeIndex)) -> &mut Self::Output {
        self.get_edge_data_mut(e.0, e.1)
    }
}
// edge:1 ends here

// nodes

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*nodes][nodes:1]]
pub struct Nodes<'a, N, E>
where
    N: Default,
    E: Default,
{
    /// An iterator over graph node indices.
    nodes: std::vec::IntoIter<NodeIndex>,

    /// Parent graph struct.
    parent: &'a NxGraph<N, E>,
}

impl<'a, N, E> Nodes<'a, N, E>
where
    N: Default,
    E: Default,
{
    fn new(g: &'a NxGraph<N, E>) -> Self {
        let nodes: Vec<_> = g.graph.node_indices().collect();

        Self {
            parent: g,
            nodes: nodes.into_iter(),
        }
    }
}

impl<'a, N, E> Iterator for Nodes<'a, N, E>
where
    N: Default,
    E: Default,
{
    type Item = (NodeIndex, &'a N);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(cur) = self.nodes.next() {
            Some((cur, &self.parent.graph[cur]))
        } else {
            None
        }
    }
}

impl<'a, N, E> std::ops::Index<NodeIndex> for Nodes<'a, N, E>
where
    N: Default,
    E: Default,
{
    type Output = N;

    fn index(&self, n: NodeIndex) -> &Self::Output {
        &self.parent[n]
    }
}
// nodes:1 ends here

// edges

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*edges][edges:1]]
pub struct Edges<'a, N, E>
where
    N: Default,
    E: Default,
{
    /// Parent graph struct
    parent: &'a NxGraph<N, E>,

    /// An iterator over graph edge indices
    edges: std::vec::IntoIter<EdgeIndex>,
}

impl<'a, N, E> Edges<'a, N, E>
where
    N: Default,
    E: Default,
{
    fn new(g: &'a NxGraph<N, E>) -> Self {
        let edges: Vec<_> = g.graph.edge_indices().collect();

        Self {
            parent: g,
            edges: edges.into_iter(),
        }
    }
}

impl<'a, N, E> Iterator for Edges<'a, N, E>
where
    N: Default,
    E: Default,
{
    type Item = (NodeIndex, NodeIndex, &'a E);

    /// Returns a tuple in (index_i, index_j, Edge) format.
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(cur) = self.edges.next() {
            let (u, v) = self
                .parent
                .graph
                .edge_endpoints(cur)
                .expect("no graph endpoints");
            let edge_data = &self.parent.graph[cur];
            Some((u, v, edge_data))
        } else {
            None
        }
    }
}

impl<'a, N, E> std::ops::Index<(NodeIndex, NodeIndex)> for Edges<'a, N, E>
where
    N: Default,
    E: Default,
{
    type Output = E;

    fn index(&self, e: (NodeIndex, NodeIndex)) -> &Self::Output {
        &self.parent[e]
    }
}
// edges:1 ends here

// pub

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*pub][pub:1]]
impl<N, E> NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    /// A Node view of the Graph.
    pub fn nodes(&self) -> Nodes<N, E> {
        Nodes::new(self)
    }

    /// An Edge view of the Graph.
    pub fn edges(&self) -> Edges<N, E> {
        Edges::new(self)
    }
}
// pub:1 ends here

// test

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*test][test:1]]
#[cfg(test)]
mod test {
    use super::*;

    #[derive(Default, Debug)]
    struct Edge {
        weight: f64,
    }

    #[derive(Default, Debug)]
    struct Node {
        /// The Cartesian position of this `Node`.
        position: [f64; 3],
    }

    #[test]
    fn test_graph() {
        // add and remove nodes
        let mut g = NxGraph::new();
        let n1 = g.add_node(Node::default());
        let n2 = g.add_node(Node::default());
        let n3 = g.add_node(Node::default());
        g.add_edge(n1, n2, Edge::default());
        g.add_edge(n1, n3, Edge::default());
        let n4 = g.add_node(Node::default());
        g.remove_node(n4);
        assert_eq!(g.number_of_nodes(), 3);
        assert_eq!(g.number_of_edges(), 2);

        // test graph
        assert!(g.has_node(n1));
        assert!(g.has_edge(n1, n2));
        assert!(!g.has_edge(n2, n3));
        g.remove_edge(n1, n3);
        assert_eq!(g.number_of_edges(), 1);
        assert!(!g.has_edge(n1, n3));

        // edit node attributes
        g[n1].position = [1.9; 3];
        // node view
        let nodes = g.nodes();
        assert_eq!(nodes[n1].position, [1.9; 3]);

        // edit edge attributes
        g[(n1, n2)].weight = 0.3;
        // edge view
        let edges = g.edges();
        assert_eq!(edges[(n1, n2)].weight, 0.3);

        let nodes = g.nodes();
        assert_eq!(nodes[n1].position, [1.9; 3]);
        let edges = g.edges();
        assert_eq!(edges[(n2, n1)].weight, 0.3);

        // loop over nodes
        for (node_index, node_data) in g.nodes() {
            dbg!(node_index, node_data);
        }

        // loop over edges
        for (u, v, edge_data) in g.edges() {
            dbg!(u, v, edge_data);
        }

        // loop over neighbors of node `n1`
        for _ in g.neighbors(n1) {
            //
        }
    }
}
// test:1 ends here
