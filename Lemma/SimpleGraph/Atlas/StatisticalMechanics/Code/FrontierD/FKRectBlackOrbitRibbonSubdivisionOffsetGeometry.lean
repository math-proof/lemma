import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionOffsetGeometry
open StatMech StatMech.FrontierD


/--
[fkRectRibbon_scaled_succ_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionOffsetGeometry.lean)
-/
@[path]
private lemma fkRectRibbon_scaled_succ_general_eq
  {M S : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M)
  (hS : 0 < S) :
-- imply
  (((S * (finitePeriodicSucc hM i).val : Nat) : Int) : ZMod (M * S)) = (((S * i.val : Nat) : Int) : ZMod (M * S)) + S := by
-- proof
  apply StatMech.FrontierD.fkRectRibbon_scaled_succ_general hM hS i

/--
[fkRectRibbon_scaled_pred_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionOffsetGeometry.lean)
-/
@[path]
private lemma fkRectRibbon_scaled_pred_general_eq
  {M S : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M)
  (hS : 0 < S) :
-- imply
  (((S * (SixVertexArrows.cyclicPred hM i).val : Nat) : Int) : ZMod (M * S)) = (((S * i.val : Nat) : Int) : ZMod (M * S)) - S := by
-- proof
  apply StatMech.FrontierD.fkRectRibbon_scaled_pred_general hM hS i

/--
[fkRectRibbonSubdivisionCodeEmbed_offset_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionOffsetGeometry.lean)
-/
@[path]
private lemma fkRectRibbonSubdivisionCodeEmbed_offset_succ_eq
  {p : ZMod width × ZMod height}
  {mu : Fin 4}
  {r : Fin (onsAnisotropicStepScale width height mu)}
-- given
  (width height : ℕ)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (hr : r.val + 1 < onsAnisotropicStepScale width height mu) :
-- imply
  fkRectRibbonSubdivisionCodeEmbed width height (fkRectRibbonSubdivisionCode width height hwidth hheight p mu ⟨r.val + 1, hr⟩) = ons_dirStep (width * height) mu (fkRectRibbonSubdivisionCodeEmbed width height (fkRectRibbonSubdivisionCode width height hwidth hheight p mu r)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonSubdivisionCodeEmbed_offset_succ width height hwidth hheight p mu r hr

/--
[fkRectRibbonSubdivisionCodeEmbed_offset_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionOffsetGeometry.lean)
-/
@[path]
private lemma fkRectRibbonSubdivisionCodeEmbed_offset_zero_eq
  {p : ZMod width × ZMod height}
  {mu : Fin 4}
  {r : Fin (onsAnisotropicStepScale width height mu)}
-- given
  (width height : ℕ)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (hr : r.val = 0) :
-- imply
  fkRectRibbonSubdivisionCodeEmbed width height (fkRectRibbonSubdivisionCode width height hwidth hheight p mu r) = ((((height * p.1.val : Nat) : Int) : ZMod (width * height)), (((width * p.2.val : Nat) : Int) : ZMod (width * height))) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonSubdivisionCodeEmbed_offset_zero width height hwidth hheight p mu r hr

/--
[fkRectRibbonSubdivisionCodeEmbed_offset_wrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionOffsetGeometry.lean)
-/
@[path]
private lemma fkRectRibbonSubdivisionCodeEmbed_offset_wrap_eq
  {p : ZMod width × ZMod height}
  {mu nu : Fin 4}
  {r : Fin (onsAnisotropicStepScale width height mu)}
  {s : Fin (onsAnisotropicStepScale width height nu)}
-- given
  (width height : ℕ)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (hr : ¬ r.val + 1 < onsAnisotropicStepScale width height mu)
  (hs : s.val = 0) :
-- imply
  fkRectRibbonSubdivisionCodeEmbed width height (fkRectRibbonSubdivisionCode width height hwidth hheight (fkRectRibbonRectStep width height mu p) nu s) = ons_dirStep (width * height) mu (fkRectRibbonSubdivisionCodeEmbed width height (fkRectRibbonSubdivisionCode width height hwidth hheight p mu r)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonSubdivisionCodeEmbed_offset_wrap width height hwidth hheight p mu nu r hr s hs


-- created on 2026-10-23
