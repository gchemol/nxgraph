// [[file:../nxgraph.note::*imports][imports:1]]
use serde::*;
use std::collections::HashMap;

use petgraph::prelude::*;
// imports:1 ends here

// [[file:../nxgraph.note::*exports][exports:1]]
pub use petgraph::prelude::NodeIndex;
// exports:1 ends here

// [[file:../nxgraph.note::dfa4e9ef][dfa4e9ef]]
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
/// networkx-like API wrapper around petgraph
pub struct NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    mapping: HashMap<String, EdgeIndex>,
    graph: StableUnGraph<N, E>,
}

/// return sorted node pair as mapping key.
// NOTE: if we return a tuple or array, we will encounter not string
// key error for serde_json
fn node_pair_key(n1: NodeIndex, n2: NodeIndex) -> String {
    let v = if n1 > n2 { [n2, n1] } else { [n1, n2] };
    format!("{}-{}", v[0].index(), v[1].index())
}

impl<N, E> NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    fn edge_index_between(&self, n1: NodeIndex, n2: NodeIndex) -> Option<EdgeIndex> {
        // this is slow
        // self.graph.find_edge(n1, n2)

        // make sure n1 is always smaller than n2.
        // let (n1, n2) = if n1 > n2 { (n2, n1) } else { (n1, n2) };

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
        let edge_index = self.edge_index_between(node1, node2).expect("no edge index");
        self.graph.edge_weight(edge_index).expect("no edge")
    }

    /// Return a mutable reference of data associated with edge `node1--node2`.
    fn get_edge_data_mut(&mut self, node1: NodeIndex, node2: NodeIndex) -> &mut E {
        let edge_index = self.edge_index_between(node1, node2).expect("no edge index");
        self.graph.edge_weight_mut(edge_index).expect("no edge")
    }
}
// dfa4e9ef ends here

// [[file:../nxgraph.note::*base][base:1]]
/// Build/Read/Edit Graph
///
/// # Example
///
/// ```
/// use gchemol_graph::NxGraph;
/// 
/// let mut g = NxGraph::path_graph(2);
/// let u = g.add_node(2);
/// let v = g.add_node(3);
/// g.add_edge(u, v, 5);
/// 
/// assert!(g.has_node(u));
/// assert!(g.has_edge(u, v));
/// 
/// // loop over neighbors of node u
/// for x in g.neighbors(u) {
///     dbg!(x);
/// }
/// ```
///
impl<N, E> NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    /// Build a default Graph
    pub fn new() -> Self {
        Self { ..Default::default() }
    }

    /// Returns an iterator over all neighbors of node `n`.
    ///
    /// # Reference
    ///
    /// * https://networkx.github.io/documentation/stable/reference/classes/generated/networkx.Graph.neighbors.html
    pub fn neighbors(&self, n: NodeIndex) -> impl Iterator<Item = NodeIndex> + '_ {
        self.graph.neighbors(n)
    }

    /// Return an iterator over the node indices of the graph
    pub fn node_indices(&self) -> impl Iterator<Item = NodeIndex> + '_ {
        self.graph.node_indices()
    }

    /// Returns true if the graph contains the node n.
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

    /// Add a node with associated data into graph.
    pub fn add_node(&mut self, data: N) -> NodeIndex {
        self.graph.add_node(data)
    }

    /// Add multiple nodes.
    pub fn add_nodes_from<M: IntoIterator<Item = N>>(&mut self, nodes: M) -> Vec<NodeIndex> {
        nodes.into_iter().map(|node| self.add_node(node)).collect()
    }

    /// Add an edge with `data` between `u` and `v` (no parallel edge). If edge
    /// u--v already exists, the associated data will be updated.
    ///
    /// # Panics
    ///
    /// * To avoid self-loop, this method will panic if node `u` and `v` are the
    /// same.
    pub fn add_edge(&mut self, u: NodeIndex, v: NodeIndex, data: E) {
        assert_ne!(u, v, "self-loop is not allowed!");

        // not add_edge for avoidding parallel edges
        let e = self.graph.update_edge(u, v, data);

        // update node pair to edge index mapping.
        self.mapping.insert(node_pair_key(u, v), e);
    }

    /// Add multiple edges from `edges`.
    pub fn add_edges_from<M: IntoIterator<Item = (NodeIndex, NodeIndex, E)>>(&mut self, edges: M) {
        for (u, v, d) in edges {
            self.add_edge(u, v, d);
        }
    }

    /// Remove an edge between `node1` and `node2`. Return None if trying to
    /// remove a non-existent edge.
    pub fn remove_edge(&mut self, node1: NodeIndex, node2: NodeIndex) -> Option<E> {
        if let Some(e) = self.mapping.remove(&node_pair_key(node1, node2)) {
            self.graph.remove_edge(e)
        } else {
            None
        }
    }

    /// Removes the node `n` and all adjacent edges. Return None if trying to
    /// remove a non-existent node.
    pub fn remove_node(&mut self, n: NodeIndex) -> Option<N> {
        self.graph.remove_node(n)
    }

    /// Remove all nodes and edges
    pub fn clear(&mut self) {
        self.graph.clear();
    }

    /// Remove all edges
    pub fn clear_edges(&mut self) {
        self.graph.clear_edges()
    }
}
// base:1 ends here

// [[file:../nxgraph.note::*extra][extra:1]]
impl<N, E> NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    /// Provides read access to raw Graph struct.
    pub fn raw_graph(&self) -> &StableUnGraph<N, E> {
        &self.graph
    }

    /// Provides mut access to raw Graph struct.
    pub fn raw_graph_mut(&mut self) -> &mut StableUnGraph<N, E> {
        &mut self.graph
    }
}
// extra:1 ends here

// [[file:../nxgraph.note::a03268f7][a03268f7]]
#[cfg(feature = "adhoc")]
impl<N, E> NxGraph<N, E>
where
    N: Default + Clone,
    E: Default + Clone,
{
    /// Return the `Node` associated with node index `n`. Return None if no such
    /// node `n`.
    pub fn get_node(&self, n: NodeIndex) -> Option<&N> {
        self.graph.node_weight(n)
    }

    /// Return the associated edge data between node `u` and `v`. Return None if
    /// no such edge.
    pub fn get_edge(&self, u: NodeIndex, v: NodeIndex) -> Option<&E> {
        let ei = self.edge_index_between(u, v)?;
        self.graph.edge_weight(ei)
    }

    /// Return mutable access to the associated edge data between node `u` and `v`. Return None if
    /// no such edge.
    pub fn get_edge_mut(&mut self, u: NodeIndex, v: NodeIndex) -> Option<&mut E> {
        let ei = self.edge_index_between(u, v)?;
        self.graph.edge_weight_mut(ei)
    }
}
// a03268f7 ends here

// [[file:../nxgraph.note::d04c099c][d04c099c]]
/// Methods for creating `NxGraph` struct
impl<N, E> NxGraph<N, E>
where
    N: Default + Clone,
    E: Default + Clone,
{
    /// Return `NxGraph` from raw petgraph struct.
    pub fn from_raw_graph(graph: StableUnGraph<N, E>) -> Self {
        let edges: Vec<_> = graph
            .edge_indices()
            .map(|e| {
                let (u, v) = graph.edge_endpoints(e).unwrap();
                let edata = graph.edge_weight(e).unwrap().to_owned();
                (u, v, edata)
            })
            .collect();

        let mut g = Self { graph, ..Default::default() };
        g.add_edges_from(edges);
        g
    }
}

impl NxGraph<usize, usize> {
    /// Returns the Path graph `P_n` of linearly connected nodes. Node data and
    /// edge data are usize type, mainly for test purpose.
    pub fn path_graph(n: usize) -> Self {
        let mut g = Self::new();
        let nodes = g.add_nodes_from(1..=n);

        for p in nodes.windows(2) {
            g.add_edge(p[0], p[1], 0)
        }

        g
    }
}

#[test]
fn test_path_graph() {
    let g = NxGraph::path_graph(5);
    assert_eq!(g.number_of_nodes(), 5);
    assert_eq!(g.number_of_edges(), 4);
}
// d04c099c ends here

// [[file:../nxgraph.note::*node][node:1]]
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

// [[file:../nxgraph.note::*edge][edge:1]]
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

// [[file:../nxgraph.note::*nodes][nodes:1]]
/// Node view of graph, created with [nodes](struct.NxGraph.html#method.nodes) method.
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

// [[file:../nxgraph.note::*edges][edges:1]]
/// Edge view of graph, created with [edges](struct.NxGraph.html#method.edges) method.
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

// [[file:../nxgraph.note::*pub][pub:1]]
/// Node view and Edge view for `NxGraph`.
///
/// # Example
///
/// ```
/// use gchemol_graph::NxGraph;
/// 
/// let mut g = NxGraph::path_graph(3);
/// let u = g.add_node(5);
/// let v = g.add_node(2);
/// let w = g.add_node(1);
/// g.add_edge(u, v, 7);
/// g.add_edge(u, w, 6);
/// 
/// // loop over nodes
/// for (node_index, node_data) in g.nodes() {
///     // do something
/// }
/// 
/// // get node data of node `u`
/// let nodes = g.nodes();
/// let node_u = nodes[u];
/// assert_eq!(node_u, 5);
/// 
/// // Collect nodes into HashMap
/// let nodes: std::collections::HashMap<_, _> = g.nodes().collect();
/// assert_eq!(nodes.len(), 6);
/// 
/// // loop over edges
/// for (u, v, edge_data) in g.edges() {
///     // dbg!(u, v, edge_data)
/// }
/// 
/// // get edge data
/// let edges = g.edges();
/// let edge_uv = edges[(u, v)];
/// assert_eq!(edge_uv, 7);
/// ```
impl<N, E> NxGraph<N, E>
where
    N: Default,
    E: Default,
{
    /// A Node view of the Graph.
    ///
    /// # Reference
    ///
    /// * https://networkx.github.io/documentation/stable/reference/classes/generated/networkx.Graph.nodes.html
    pub fn nodes(&self) -> Nodes<N, E> {
        Nodes::new(self)
    }

    /// An Edge view of the Graph.
    ///
    /// # Reference
    ///
    /// * https://networkx.github.io/documentation/stable/reference/classes/generated/networkx.Graph.edges.html
    pub fn edges(&self) -> Edges<N, E> {
        Edges::new(self)
    }
}
// pub:1 ends here

// [[file:../nxgraph.note::*test][test:1]]
#[cfg(test)]
mod test {
    use super::*;

    #[derive(Clone, Default, Debug, PartialEq)]
    struct Edge {
        weight: f64,
    }

    impl Edge {
        fn new(weight: f64) -> Self {
            Self { weight }
        }
    }

    #[derive(Clone, Default, Debug, PartialEq)]
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

        // add edges
        g.add_edge(n1, n2, Edge { weight: 1.0 });
        assert_eq!(1, g.number_of_edges());

        // add edge n1-n2 again. Note: no parallel edge
        g.add_edge(n1, n2, Edge { weight: 2.0 });
        assert_eq!(1, g.number_of_edges());
        // edge data has been udpated
        assert_eq!(g[(n1, n2)].weight, 2.0);

        g.add_edge(n1, n3, Edge::default());
        let n4 = g.add_node(Node::default());
        let _ = g.remove_node(n4);
        assert_eq!(g.number_of_nodes(), 3);
        assert_eq!(g.number_of_edges(), 2);

        // test remove node and edge
        let node = Node { position: [1.0; 3] };
        let n4 = g.add_node(node.clone());
        let edge = Edge { weight: 2.2 };
        g.add_edge(n1, n4, edge.clone());
        let x = g.remove_edge(n2, n4);
        assert_eq!(x, None);
        let x = g.remove_edge(n1, n4);
        assert_eq!(x, Some(edge));
        let x = g.remove_node(n4);
        assert_eq!(x, Some(node));

        // test graph
        assert!(g.has_node(n1));
        assert!(g.has_edge(n1, n2));
        assert!(!g.has_edge(n2, n3));
        let _ = g.remove_edge(n1, n3);
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
        assert_eq!(edges[(n2, n1)].weight, 0.3);

        // loop over nodes
        for (u, node_data) in g.nodes() {
            dbg!(u, node_data);
        }

        // loop over edges
        for (u, v, edge_data) in g.edges() {
            dbg!(u, v, edge_data);
        }

        // loop over neighbors of node `n1`
        for u in g.neighbors(n1) {
            dbg!(&g[u]);
        }

        // clear graph
        g.clear();
        assert_eq!(g.number_of_nodes(), 0);
        assert_eq!(g.number_of_edges(), 0);
    }

    #[test]
    #[should_panic]
    fn test_speical_graph() {
        let mut g = NxGraph::new();
        let n1 = g.add_node(Node::default());
        let n2 = g.add_node(Node::default());

        g.add_edge(n1, n2, Edge::new(1.0));
        assert_eq!(g[(n1, n2)].weight, 1.0);
        assert_eq!(g[(n2, n1)].weight, 1.0);

        // parallel edge is avoided
        g.add_edge(n2, n1, Edge::new(2.0));
        assert_eq!(g[(n1, n2)].weight, 2.0);

        // self-loop is not allowed
        g.add_edge(n2, n2, Edge::default());
    }
}
// test:1 ends here
