import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvWeight_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k : ℕ}
  (r : Fin m → ℕ) (i : RothMvIndex m)
-- given
  (hk : 0 < k)
  (hr : ∀ h, 0 < r h) :
-- imply
  rothMvWeight (fun h ↦ k * r h) i = rothMvWeight r i / k := by
-- proof
  unfold rothMvWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hrR : (r h : ℝ) ≠ 0 := by exact_mod_cast (hr h).ne'
  push_cast
  field_simp


-- created on 2026-10-21
