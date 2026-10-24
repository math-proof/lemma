import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.BlockCirculant2D
open StatMech StatMech.Onsager


/--
[ons_det_blockCirculant2D](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/BlockCirculant2D.lean)
-/
@[path]
private lemma ons_det_blockCirculant2D_eq
  {L d : ℕ}
  [NeZero L]
  {ω : ℂ}
  {v : (ZMod L × ZMod L) → Matrix (Fin d) (Fin d) ℂ}
-- given
  (hω : IsPrimitiveRoot ω L) :
-- imply
  (ons_blockCirculant2D L d v).det = ∏ j : ZMod L × ZMod L, (ons_blockSymbol2D L d ω v j).det := by
-- proof
  apply StatMech.Onsager.ons_det_blockCirculant2D L d ω hω v


-- created on 2026-10-23
