import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleWeighted.Part2
open StatMech StatMech.Onsager


/--
[ons_rectKWmatDartWeighted_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleWeighted.lean)
-/
@[path]
private lemma ons_rectKWmatDartWeighted_const_eq
  {M N : Nat}
  {x : Complex} :
-- imply
  ons_rectKWmatDartWeighted M N (fun _ => x) = ons_rectKWmat M N x := by
-- proof
  apply StatMech.Onsager.ons_rectKWmatDartWeighted_const M N x

/--
[norm_diagonal_rectDartWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleWeighted.lean)
-/
@[path]
private lemma norm_diagonal_rectDartWeight_le_eq
  {M N : Nat}
  {q : Real}
-- given
  (weight : ons_RectDart M N -> Complex)
  (hq : 0 <= q)
  (hweight : forall d, ‖weight d‖ <= q) :
-- imply
  letI : NormedRing (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) := by
-- proof
  apply StatMech.Onsager.norm_diagonal_rectDartWeight_le M N weight q hq hweight

/--
[norm_ons_rectKWmatDartWeighted_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleWeighted.lean)
-/
@[path]
private lemma norm_ons_rectKWmatDartWeighted_sharp_eq
  {M N : Nat}
  {q : Real}
-- given
  (weight : ons_RectDart M N -> Complex)
  (hq : 0 <= q)
  (hweight : forall d, ‖weight d‖ <= q) :
-- imply
  letI : NormedRing (Matrix (ons_RectDart M N) (ons_RectDart M N) Complex) := by
-- proof
  apply StatMech.Onsager.norm_ons_rectKWmatDartWeighted_sharp M N weight q hq hweight

/--
[norm_root_ons_rectKWmatDartWeighted_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleWeighted.lean)
-/
@[path]
private lemma norm_root_ons_rectKWmatDartWeighted_le_eq
  {M N : Nat}
  {q : Real}
  {alpha : Complex}
-- given
  (weight : ons_RectDart M N -> Complex)
  (hq : 0 <= q)
  (hweight : forall d, ‖weight d‖ <= q)
  (halpha : alpha ∈ (ons_rectKWmatDartWeighted M N weight).charpoly.roots) :
-- imply
  ‖alpha‖ <= (Real.sqrt 2 + 1) * q := by
-- proof
  apply StatMech.Onsager.norm_root_ons_rectKWmatDartWeighted_le M N weight q hq hweight alpha halpha

/--
[ons_rectKWmatDartWeighted_spectral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleWeighted.lean)
-/
@[path]
private lemma ons_rectKWmatDartWeighted_spectral_eq
  {M N : Nat}
  {q : Real}
-- given
  (weight : ons_RectDart M N -> Complex)
  (hq0 : 0 <= q)
  (hq : q < ons_signedLoopCriticalWeight)
  (hweight : forall d, ‖weight d‖ <= q) :
-- imply
  ∀ alpha ∈ (ons_rectKWmatDartWeighted M N weight).charpoly.roots, ‖alpha‖ < 1 := by
-- proof
  apply StatMech.Onsager.ons_rectKWmatDartWeighted_spectral M N weight q hq0 hq hweight

/--
[ons_rectKWmatDartWeighted_det_eq_walk_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleWeighted.lean)
-/
@[path]
private lemma ons_rectKWmatDartWeighted_det_eq_walk_exp_eq
  {M N : Nat}
  {q : Real}
-- given
  (weight : ons_RectDart M N -> Complex)
  (hq0 : 0 <= q)
  (hq : q < ons_signedLoopCriticalWeight)
  (hweight : forall d, ‖weight d‖ <= q) :
-- imply
  (1 - ons_rectKWmatDartWeighted M N weight).det = Complex.exp (- ∑' n : Nat, (∑ v : Fin (n + 1) -> ons_RectDart M N, ∏ k : Fin (n + 1), ons_rectKWmatDartWeighted M N weight (v k) (v (k + 1))) / (n + 1)) := by
-- proof
  apply StatMech.Onsager.ons_rectKWmatDartWeighted_det_eq_walk_exp M N weight q hq0 hq hweight

/--
[norm_ons_rectDartSignDefect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleWeighted.lean)
-/
@[path]
private lemma norm_ons_rectDartSignDefect_eq
  {M N : Nat}
  [DecidablePred defect]
  {q : Real}
  {d : ons_RectDart M N}
-- given
  (defect : ons_RectDart M N -> Prop)
  (hq : 0 <= q) :
-- imply
  ‖ons_rectDartSignDefect M N defect q d‖ = q := by
-- proof
  apply StatMech.Onsager.norm_ons_rectDartSignDefect M N defect hq d

/--
[ons_rectSignDefect_det_ratio_eq_walk_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleWeighted.lean)
-/
@[path]
private lemma ons_rectSignDefect_det_ratio_eq_walk_exp_eq
  {M N : Nat}
  [DecidablePred defect]
  {q : Real}
-- given
  (defect : ons_RectDart M N -> Prop)
  (hq0 : 0 <= q)
  (hq : q < ons_signedLoopCriticalWeight) :
-- imply
  (1 - ons_rectKWmatDartWeighted M N (ons_rectDartSignDefect M N defect q)).det / (1 - ons_rectKWmat M N (q : Complex)).det = Complex.exp (-(ons_rectWeightedWalkExponent M N (ons_rectDartSignDefect M N defect q) - ons_rectWeightedWalkExponent M N (fun _ => (q : Complex)))) := by
-- proof
  apply StatMech.Onsager.ons_rectSignDefect_det_ratio_eq_walk_exp M N defect q hq0 hq


-- created on 2026-10-23
