// element.rs
// :PROPERTIES:
// :header-args: :tangle tests/element.rs
// :END:

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*element.rs][element.rs:1]]
#[derive(Default, Debug)]
struct Bond {
    order: f64,
}

impl Bond {
    fn new(b: f64) -> Self {
        Self { order: b }
    }
}

#[derive(Default, Debug)]
struct Atom {
    /// Element symbol
    symbol: String,
}

impl Atom {
    fn new(symbol: &str) -> Self {
        Self { symbol: symbol.into() }
    }
}

#[test]
#[cfg(feature = "adhoc")]
fn test() {
    // for combinations method
    use itertools::*;

    let elements = vec!["C", "H", "O", "N"];

    let mut g = gchemol_graph::NxGraph::new();

    // create graph node for each element
    let nodes = g.add_nodes_from(elements.into_iter().map(|e| Atom::new(e)));

    // create all possible edges
    let edges = nodes.iter().combinations(2).map(|p| (*p[0], *p[1], Bond::new(1.2)));

    g.add_edges_from(edges);

    assert_eq!(g.number_of_nodes(), 4);
    assert_eq!(g.number_of_edges(), 6);

    // view atoms
    let atoms = g.nodes();
    let n0 = nodes[0];
    let n1 = nodes[1];
    let n2 = nodes[2];
    let n3 = nodes[3];

    assert_eq!(atoms[n0].symbol, "C");
    assert_eq!(atoms[n1].symbol, "H");
    assert_eq!(atoms[n2].symbol, "O");
    assert_eq!(atoms[n3].symbol, "N");

    // view bonds
    let bonds = g.edges();
    let b1 = &bonds[(n0, n1)];
    let b2 = &bonds[(n0, n2)];
    assert_eq!(b1.order, b2.order);
}
// element.rs:1 ends here
