module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothWeight_eq_centeredSum_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothWeight.eq.AddRothCenteredSumDiv_2.of.RothBox
  {m : ℕ}
-- given
  (r : Fin m → ℕ)
  (j : RothBox r) :
-- imply
  rothWeight r (fun h ↦ j h) = rothCenteredSum r j + (m : ℝ) / 2 := by
-- proof
  unfold rothWeight rothCenteredSum rothCentered
  rw [Finset.sum_sub_distrib]
  simp
  ring


-- updated on 2026-11-13
-- created on 2026-10-21
