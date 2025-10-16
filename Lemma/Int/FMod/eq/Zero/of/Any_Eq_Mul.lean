import Lemma.Int.FMod.eq.Sub_MulFDiv
import Lemma.Bool.Ne.is.NotEq
open Bool Int


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : ∃ k : ℤ, n = k * d) :
-- imply
  n.fmod d = 0 := by
-- proof
  let ⟨k, h⟩ := h
  rw [h]
  rw [FMod.eq.Sub_MulFDiv]
  by_cases h : d = 0 <;>
  ·
    simp_all


-- created on 2025-03-30
