import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.BlockCirculant
open StatMech StatMech.Onsager


/--
[ons_det_blockCirculant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/BlockCirculant.lean)
-/
@[path]
private lemma ons_det_blockCirculant_eq
  {n d : ℕ}
  [NeZero n]
  {ω : ℂ}
  {v : ZMod n → Matrix (Fin d) (Fin d) ℂ}
-- given
  (hω : IsPrimitiveRoot ω n) :
-- imply
  (ons_blockCirculant n d v).det = ∏ j : ZMod n, (ons_blockSymbol n d ω v j).det := by
-- proof
  apply StatMech.Onsager.ons_det_blockCirculant n d ω hω v


-- created on 2026-10-23
