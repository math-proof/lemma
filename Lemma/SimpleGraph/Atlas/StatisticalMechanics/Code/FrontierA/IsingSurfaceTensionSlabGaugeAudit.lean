import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSlabGaugeAudit
open Finset StatMech StatMech.FrontierA


/--
[multibondDisorderFreeEnergy_sheet_eq_lowerComplementSurface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSlabGaugeAudit.lean)
-/
@[path]
private lemma multibondDisorderFreeEnergy_sheet_eq_lowerComplementSurface_eq
  {a b c : Nat}
  {k : Fin (c + 1)}
-- given
  (hk : 0 < k.val)
  (J : CubicalPlaquette a b c -> Real) :
-- imply
  multibondDisorderFreeEnergy (cubicalDualEnds (a := a) (b := b) (c := c)) J (cubicalXYSheet (a := a) (b := b) (c := c) k) = multibondDisorderFreeEnergy (cubicalDualEnds (a := a) (b := b) (c := c)) J (cubicalLowerComplementSurface (a := a) (b := b) (c := c) k) := by
-- proof
  apply StatMech.FrontierA.multibondDisorderFreeEnergy_sheet_eq_lowerComplementSurface k hk J


-- created on 2026-10-23
