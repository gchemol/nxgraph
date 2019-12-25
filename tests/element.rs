// element.rs
// :PROPERTIES:
// :header-args: :tangle tests/element.rs
// :END:

// [[file:~/Workspace/Programming/gchemol-rs/nxgraph/nxgraph.note::*element.rs][element.rs:1]]
#[derive(Default, Debug)]
struct Bond {
    r0: f64,
    b: f64,
}

impl Bond {
    fn new(r0: f64, b: f64) -> Self {
        Self { r0, b }
    }
}

#[derive(Default, Debug)]
struct Atom {
    /// Element symbol
    symbol: String,
}

impl Atom {
    fn new(symbol: &str) -> Self {
        Self {
            symbol: symbol.into(),
        }
    }
}

#[test]
fn test() {
    let elements = vec!["C", "H", "O", "N"];

    let mut g = nxgraph::NxGraph::new();

    // create graph node for each element
    let nodes: Vec<_> = elements
        .into_iter()
        .map(|symbol| {
            let atom = Atom::new(symbol);
            g.add_node(atom)
        })
        .collect();

    // create all possible edges with self-loop
    let n = nodes.len();
    for i in 0..n {
        for j in i..n {
            dbg!((i, j));
            g.add_edge(nodes[i], nodes[j], Bond::new(1.2, 0.37));
        }
    }

    let n1 = nodes[1];
    let n2 = nodes[2];
    dbg!(&g[(n1, n2)]);
    dbg!(&g[(n2, n1)]);
}
// element.rs:1 ends here
