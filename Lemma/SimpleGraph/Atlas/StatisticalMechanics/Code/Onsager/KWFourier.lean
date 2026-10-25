import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWFourier
open StatMech StatMech.Onsager


/--
[ons_KWmat_eq_blockCirc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWFourier.lean)
-/
@[path]
private lemma ons_KWmat_eq_blockCirc_eq
  {L : ℕ}
  {x ωt : ℂ} :
-- imply
  ons_KWmat L x ωt = ons_blockCirculant2D L 4 (ons_KWblock L x ωt) := by
-- proof
  apply StatMech.Onsager.ons_KWmat_eq_blockCirc L x ωt

/--
[ons_KWblockSymbol_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWFourier.lean)
-/
@[path]
private lemma ons_KWblockSymbol_eq_eq
  {L : ℕ}
  [NeZero L]
  [Fact (1 < L)]
  {x ωt ωL : ℂ}
  {j : ZMod L × ZMod L}
-- given
  (hωt : ωt^2 = Complex.I)
  (hωL : IsPrimitiveRoot ωL L) :
-- imply
  ons_blockSymbol2D L 4 ωL (fun g => (if g = 0 then (1:Matrix (Fin 4) (Fin 4) ℂ) else 0) - ons_KWblock L x ωt g) j = ons_KWsymbolMat x ωt (ωL ^ j.1.val) (ωL ^ j.2.val) := by
-- proof
  apply StatMech.Onsager.ons_KWblockSymbol_eq L x ωt ωL hωt hωL j

/--
[ons_KWmat_det_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWFourier.lean)
-/
@[path]
private lemma ons_KWmat_det_eq_prod_eq
  {L : ℕ}
  [NeZero L]
  [Fact (1 < L)]
  {x ωt ωL : ℂ}
-- given
  (hωt : ωt^2 = Complex.I)
  (hωL : IsPrimitiveRoot ωL L) :
-- imply
  (1 - ons_KWmat L x ωt).det = ∏ j : ZMod L × ZMod L, ((1 + x^2)^2 - x*(1 - x^2)*((ωL^j.1.val) + (ωL^j.1.val)⁻¹ + (ωL^j.2.val) + (ωL^j.2.val)⁻¹)) := by
-- proof
  apply StatMech.Onsager.ons_KWmat_det_eq_prod L x ωt ωL hωt hωL


-- created on 2026-10-23
