type Vertex = nat
type Edge = (Vertex, Vertex)

datatype Tree = Leaf(vertex: Vertex) | Node(vertex: Vertex, children: seq<Tree>)

function {:induction false} VertexCount(t: Tree): nat
    decreases t, 0
{
    match t
    case Leaf(_) => 1
    case Node(_, children) => 1 + SumVertexCount(children)
}

function {:induction false} SumVertexCount(children: seq<Tree>): nat
    decreases children, 1
{
    if |children| == 0 then 0 else VertexCount(children[0]) + SumVertexCount(children[1..])
}

function {:induction false} EdgeCount(t: Tree): nat
    decreases t, 0
{
    match t case Leaf(_) => 0 case Node(_, children) => |children| + SumEdgeCount(children)
}

function {:induction false} SumEdgeCount(children: seq<Tree>): nat
    decreases children, 1
{
    if |children| == 0 then 0 else EdgeCount(children[0]) + SumEdgeCount(children[1..])
}

function TreeToEdges(t: Tree): set<Edge>
    decreases t
{
    match t
    case Leaf(_) => {}
    case Node(v, children) =>
        (set i | 0 <= i < |children| :: (v, (match children[i] case Leaf(u) => u case Node(u, _) => u))) +
        TreeToEdgesSeq(children)
}

function TreeToEdgesSeq(children: seq<Tree>): set<Edge>
    decreases children
{
    if |children| == 0 then {}
    else TreeToEdges(children[0]) + TreeToEdgesSeq(children[1..])
}

ghost predicate IsTree(edges: set<Edge>)
{
    exists t: Tree :: TreeToEdges(t) == edges
}

method TreeTest(t: Tree) {
    assert EdgeCount(t) == VertexCount(t) - 1 by {
        Proof(t);
    }
}
