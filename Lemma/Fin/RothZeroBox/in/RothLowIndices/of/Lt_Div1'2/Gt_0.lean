import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothZeroBox_mem_low](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {γ : ℝ}
-- given
  (hm : 0 < m)
  (hγ : γ < 1 / 2)
  (r : Fin m → ℕ) :
-- imply
  rothZeroBox r ∈ rothLowIndices r γ := by
-- proof
  simp only [rothLowIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hprod : (0 : ℝ) < m * (1 / 2 - γ) := mul_pos hmR (sub_pos.mpr hγ)
  simpa [rothWeight, rothZeroBox] using hprod


-- created on 2026-10-21
