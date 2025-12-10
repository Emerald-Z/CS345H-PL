// Program proofs, p. 96


lemma {:induction false} proof(x: int)
    ensures x < More(x)
{
    if (x <= 0) {
        assert x < 1;
    } else {
        // Inductive case: More(x) = More(x-2) + 3
        // Use inductive hypothesis
        proof(x-2);
        // We have x-2 < More(x-2), so x < More(x-2) + 2
        // Since 2 < 3, we get x < More(x-2) + 3 = More(x)
        assert x < More(x-2) + 2;
        assert x < More(x-2) + 3;
    }
}

