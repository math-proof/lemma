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
  simp only [Set.mem_diff, Set.mem_union, Set.mem_inter_iff, Set.mem_empty_iff_false]
  constructor
  ·
    rintro ⟨haB | hB, hA⟩
    ·
      exfalso
      apply hA haB
    ·
      exact hB
  ·
    intro hB
    constructor
    ·
      right
      assumption
    ·
      intro hA
      have := In_Inter.of.In.In hA hB
      rwa [h] at this


-- created on 2025-07-20
