import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalTwoPointPrism.Part2
open StatMech StatMech.FrontierA


/--
[typedSpinProduct_unanchorConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalTwoPointPrism.lean)
-/
@[path]
private lemma typedSpinProduct_unanchorConfig_eq
  [Fintype P]
  [DecidableEq P]
  {root x y : V}
  {b : Bool}
  {s : AnchoredConfig V root} :
-- imply
  typedSpinProduct (unanchorConfig b s) x y = typedSpinProduct s.1 x y := by
-- proof
  apply StatMech.FrontierA.typedSpinProduct_unanchorConfig root x y b s

/--
[multibondIsingTwoPointNumerator_eq_two_mul_anchored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalTwoPointPrism.lean)
-/
@[path]
private lemma multibondIsingTwoPointNumerator_eq_two_mul_anchored_eq
  [Fintype P]
  [DecidableEq P]
  {root : V}
  {x y : V}
-- given
  (ends : P -> V × V)
  (J : P -> Real) :
-- imply
  (∑ sigma : V -> Bool, multibondIsingWeight ends J sigma * typedSpinProduct sigma x y) = 2 * ∑ s : AnchoredConfig V root, multibondIsingWeight ends J s.1 * typedSpinProduct s.1 x y := by
-- proof
  apply StatMech.FrontierA.multibondIsingTwoPointNumerator_eq_two_mul_anchored root ends J x y

/--
[typedSpinProduct_oddCubical_eq_prismSpinProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalTwoPointPrism.lean)
-/
@[path]
private lemma typedSpinProduct_oddCubical_eq_prismSpinProduct_eq
  [Fintype P]
  [DecidableEq P]
  {n : Nat}
  {s : AnchoredConfig (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none}
  {q r : CubicalCell (2 * n + 1) (2 * n + 1) (2 * n + 1)} :
-- imply
  typedSpinProduct s.1 (some q) (some r) = rectangularPrismSpin (oddCubicalAnchoredEquivPrismConfig n s) (oddCubicalCellEquivPrismSite n q).x (oddCubicalCellEquivPrismSite n q).y (oddCubicalCellEquivPrismSite n q).z * rectangularPrismSpin (oddCubicalAnchoredEquivPrismConfig n s) (oddCubicalCellEquivPrismSite n r).x (oddCubicalCellEquivPrismSite n r).y (oddCubicalCellEquivPrismSite n r).z := by
-- proof
  apply StatMech.FrontierA.typedSpinProduct_oddCubical_eq_prismSpinProduct n s q r

/--
[oddCubicalAnchoredWeight_eq_plusPrismWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalTwoPointPrism.lean)
-/
@[path]
private lemma oddCubicalAnchoredWeight_eq_plusPrismWeight_eq
  [Fintype P]
  [DecidableEq P]
  {J beta : Real}
  {n : Nat}
  {s : AnchoredConfig (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none} :
-- imply
  multibondIsingWeight cubicalDualEnds (fun _ => beta * J) s.1 = Real.exp (-beta * rectangularPrismPlusEnergy J (oddCubicalAnchoredEquivPrismConfig n s)) := by
-- proof
  apply StatMech.FrontierA.oddCubicalAnchoredWeight_eq_plusPrismWeight J beta n s

/--
[oddCubicalDualTwoPoint_eq_plusPrismTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalTwoPointPrism.lean)
-/
@[path]
private lemma oddCubicalDualTwoPoint_eq_plusPrismTwoPoint_eq
  [Fintype P]
  [DecidableEq P]
  {J beta : Real}
  {n : Nat}
  {q r : CubicalCell (2 * n + 1) (2 * n + 1) (2 * n + 1)} :
-- imply
  multibondIsingTwoPoint (cubicalDualEnds (a := 2 * n + 1) (b := 2 * n + 1) (c := 2 * n + 1)) (fun _ : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) => beta * J) (some q) (some r) = oddPrismPlusTwoPoint J beta n (oddCubicalCellEquivPrismSite n q) (oddCubicalCellEquivPrismSite n r) := by
-- proof
  apply StatMech.FrontierA.oddCubicalDualTwoPoint_eq_plusPrismTwoPoint J beta n q r


-- created on 2026-10-23
