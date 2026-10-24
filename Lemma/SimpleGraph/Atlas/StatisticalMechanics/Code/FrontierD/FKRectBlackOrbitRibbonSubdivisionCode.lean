import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCode
open StatMech StatMech.FrontierD


/--
[fkRectRibbonBackwardCode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean)
-/
@[path]
private lemma fkRectRibbonBackwardCode_injective_eq
  {M S : ℕ}
-- given
  (hM : 0 < M)
  (hS : 0 < S) :
-- imply
  Function.Injective (fun z : Fin M × Fin S => fkRectRibbonBackwardCode hM hS z.1 z.2) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonBackwardCode_injective hM hS

/--
[fkRectRibbon_forward_eq_backward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean)
-/
@[path]
private lemma fkRectRibbon_forward_eq_backward_eq
  {M S : ℕ}
  {p q : Fin M}
  {r s : Fin S}
-- given
  (hM : 0 < M)
  (hS : 0 < S)
  (h : (p, r) = fkRectRibbonBackwardCode hM hS q s) :
-- imply
  (r.val = 0 ∧ s.val = 0 ∧ p = q) ∨ (r.val ≠ 0 ∧ s.val ≠ 0 ∧ p = SixVertexArrows.cyclicPred hM q ∧ r.val + s.val = S) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbon_forward_eq_backward hM hS p q r s h

/--
[fkRectZModFin_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean)
-/
@[path]
private lemma fkRectZModFin_val_eq
  {M : ℕ}
  {p : ZMod M}
-- given
  (hM : 0 < M) :
-- imply
  (fkRectZModFin hM p).val = p.val := by
-- proof
  apply StatMech.FrontierD.fkRectZModFin_val hM p

/--
[fkRectZModFin_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean)
-/
@[path]
private lemma fkRectZModFin_injective_eq
  {M : ℕ}
-- given
  (hM : 0 < M) :
-- imply
  Function.Injective (fkRectZModFin hM) := by
-- proof
  apply StatMech.FrontierD.fkRectZModFin_injective hM

/--
[fkRectZModFin_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean)
-/
@[path]
private lemma fkRectZModFin_add_one_eq
  {M : ℕ}
  {p : ZMod M}
-- given
  (hM : 0 < M) :
-- imply
  fkRectZModFin hM (p + 1) = finitePeriodicSucc hM (fkRectZModFin hM p) := by
-- proof
  apply StatMech.FrontierD.fkRectZModFin_add_one hM p

/--
[fkRectZModFin_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean)
-/
@[path]
private lemma fkRectZModFin_sub_one_eq
  {M : ℕ}
  {p : ZMod M}
-- given
  (hM : 0 < M) :
-- imply
  fkRectZModFin hM (p - 1) = SixVertexArrows.cyclicPred hM (fkRectZModFin hM p) := by
-- proof
  apply StatMech.FrontierD.fkRectZModFin_sub_one hM p

/--
[fkRectRibbonSubdivisionCode_congr_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean)
-/
@[path]
private lemma fkRectRibbonSubdivisionCode_congr_direction_eq
  {p : ZMod width × ZMod height}
  {mu nu : Fin 4}
  {r : Fin (onsAnisotropicStepScale width height mu)}
-- given
  (width height : ℕ)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (h : mu = nu) :
-- imply
  fkRectRibbonSubdivisionCode width height hwidth hheight p mu r = fkRectRibbonSubdivisionCode width height hwidth hheight p nu (fkRectRibbonSubdivisionResidueCongr width height h r) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonSubdivisionCode_congr_direction width height hwidth hheight p h r

/--
[fkRectRibbonSubdivisionCode_fixed_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean)
-/
@[path]
private lemma fkRectRibbonSubdivisionCode_fixed_injective_eq
  {p : ZMod width × ZMod height}
  {mu : Fin 4}
-- given
  (width height : ℕ)
  (hwidth : 0 < width)
  (hheight : 0 < height) :
-- imply
  Function.Injective (fkRectRibbonSubdivisionCode width height hwidth hheight p mu) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonSubdivisionCode_fixed_injective width height hwidth hheight p mu

/--
[fkRectRibbonSubdivisionCodeEmbed_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean)
-/
@[path]
private lemma fkRectRibbonSubdivisionCodeEmbed_injective_eq
  [NeZero width]
  [NeZero height]
-- given
  (width height : ℕ) :
-- imply
  Function.Injective (fkRectRibbonSubdivisionCodeEmbed width height) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonSubdivisionCodeEmbed_injective width height

/--
[fkRectFinFour_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean)
-/
@[path]
private lemma fkRectFinFour_cases_eq
  {mu : Fin 4} :
-- imply
  mu = 0 ∨ mu = 1 ∨ mu = 2 ∨ mu = 3 := by
-- proof
  apply StatMech.FrontierD.fkRectFinFour_cases mu


-- created on 2026-10-23
