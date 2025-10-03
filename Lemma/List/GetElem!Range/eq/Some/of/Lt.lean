import Lemma.List.GetElem!Range.eq.Some.is.Lt.Eq
open List


@[main]
private lemma main
  {n i : ℕ}
-- given
  (h : i < n) :
-- imply
  (List.range n)[i]? = some i :=
-- proof
  GetElem!Range.eq.Some.of.Lt.Eq h rfl


-- created on 2025-05-18
