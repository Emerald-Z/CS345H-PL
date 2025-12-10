lemma {:induction false} SumProperty(children: seq<Tree>)
    requires forall i :: 0 <= i < |children| ==> EdgeCount(children[i]) == VertexCount(children[i]) - 1
    ensures SumEdgeCount(children) == SumVertexCount(children) - |children|
{
    if |children| == 0 {
        // Base case: empty sequence
    } else {
        // first child
        assert EdgeCount(children[0]) == VertexCount(children[0]) - 1;
        SumProperty(children[1..]);
    }
}

lemma {:induction false} Proof(t: Tree)
    ensures EdgeCount(t) == VertexCount(t) - 1
{
    match t
    case Leaf(_) =>
        // Base case: Leaf has 0 edges and 1 vertex, so 0 == 1 - 1
    case Node(_, children) =>
        forall i | 0 <= i < |children| {
            Proof(children[i]);
        }
        // true forall i :: 0 <= i < |children| ==> EdgeCount(children[i]) == VertexCount(children[i]) - 1
        SumProperty(children);
        assert EdgeCount(t) == |children| + SumEdgeCount(children);
        assert VertexCount(t) == 1 + SumVertexCount(children);
}