import Lemma.Set.In_Inter.is.In.In
open Set


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ∩ B = ∅) :
-- imply
  (A ∪ B) \ A = B := by
-- proof
  ext x
  constructor
  ·
    grind
  ·
    intro hB
    constructor
    ·
      tauto
    ·
      intro hA
      have := In_Inter.of.In.In hA hB
      grind


-- created on 2025-07-20
