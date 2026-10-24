import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.Circulant
open StatMech StatMech.Onsager


/--
[ons_det_circulant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Circulant.lean)
-/
@[path]
private lemma ons_det_circulant_eq
  {n : ℕ}
  [NeZero n]
  {ω : ℂ}
  {v : Fin n → ℂ}
-- given
  (hω : IsPrimitiveRoot ω n) :
-- imply
  (Matrix.circulant v).det = ∏ j : Fin n, (∑ k : Fin n, v k * ω ^ ((k : ℕ) * (j : ℕ))) := by
-- proof
  apply StatMech.Onsager.ons_det_circulant n ω hω v


-- created on 2026-10-23
