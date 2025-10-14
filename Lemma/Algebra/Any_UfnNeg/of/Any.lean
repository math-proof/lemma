import Lemma.Int.EqNegNeg
open Int


@[main]
private lemma main
  [InvolutiveNeg α]
  {f : α → Prop}
-- given
  (h : ∃ i, f i) :
-- imply
  ∃ i, f (-i) := by
-- proof
  obtain ⟨i, fi⟩ := h
  use -i
  rwa [EqNegNeg]


-- created on 2025-08-02
