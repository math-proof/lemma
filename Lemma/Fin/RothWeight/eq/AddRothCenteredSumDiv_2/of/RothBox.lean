import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothWeight_eq_centeredSum_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
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


-- created on 2026-10-21
