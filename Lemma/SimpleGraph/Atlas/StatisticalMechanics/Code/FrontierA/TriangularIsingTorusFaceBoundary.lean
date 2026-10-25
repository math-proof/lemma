import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFaceBoundary
open StatMech StatMech.FrontierA


/--
[triangularFaceBoundaryCoeff_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean)
-/
@[path]
private lemma triangularFaceBoundaryCoeff_reverse_eq
  {L : Nat}
  {d : triangularTorusDart L}
-- given
  (lower upper : (ZMod L × ZMod L) -> ZMod 2) :
-- imply
  triangularFaceBoundaryCoeff lower upper (triangularTorusDartReverse L d) = -triangularFaceBoundaryCoeff lower upper d := by
-- proof
  apply StatMech.FrontierA.triangularFaceBoundaryCoeff_reverse lower upper d

/--
[triangularFaceBoundaryCoeff_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean)
-/
@[path]
private lemma triangularFaceBoundaryCoeff_divergence_eq
  {L : Nat}
  {p : ZMod L × ZMod L}
-- given
  (lower upper : (ZMod L × ZMod L) -> ZMod 2) :
-- imply
  (∑ a : Fin 6, triangularFaceBoundaryCoeff lower upper (p, a)) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFaceBoundaryCoeff_divergence lower upper p

/--
[triangularFaceEastCoeff_cast_mod_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean)
-/
@[path]
private lemma triangularFaceEastCoeff_cast_mod_two_eq
  {L : Nat}
  {p : ZMod L × ZMod L}
-- given
  (lower upper : (ZMod L × ZMod L) -> ZMod 2) :
-- imply
  (triangularFaceEastCoeff lower upper p : ZMod 2) = lower p + upper (p.1, p.2 - 1) := by
-- proof
  apply StatMech.FrontierA.triangularFaceEastCoeff_cast_mod_two lower upper p

/--
[triangularFaceNorthCoeff_cast_mod_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean)
-/
@[path]
private lemma triangularFaceNorthCoeff_cast_mod_two_eq
  {L : Nat}
  {p : ZMod L × ZMod L}
-- given
  (lower upper : (ZMod L × ZMod L) -> ZMod 2) :
-- imply
  (triangularFaceNorthCoeff lower upper p : ZMod 2) = lower (p.1 - 1, p.2) + upper p := by
-- proof
  apply StatMech.FrontierA.triangularFaceNorthCoeff_cast_mod_two lower upper p

/--
[triangularFaceDiagonalCoeff_cast_mod_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean)
-/
@[path]
private lemma triangularFaceDiagonalCoeff_cast_mod_two_eq
  {L : Nat}
  {p : ZMod L × ZMod L}
-- given
  (lower upper : (ZMod L × ZMod L) -> ZMod 2) :
-- imply
  (triangularFaceDiagonalCoeff lower upper p : ZMod 2) = lower p + upper p := by
-- proof
  apply StatMech.FrontierA.triangularFaceDiagonalCoeff_cast_mod_two lower upper p

/--
[triangularFaceCoeff_eq_zero_of_cast_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean)
-/
@[path]
private lemma triangularFaceCoeff_eq_zero_of_cast_eq_zero_eq
  {a b : ZMod 2}
-- given
  (h : ((((a.val : Int) - (b.val : Int) : Int)) : ZMod 2) = 0) :
-- imply
  (a.val : Int) - b.val = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFaceCoeff_eq_zero_of_cast_eq_zero a b h

/--
[triangularFaceCoeff_ne_zero_of_cast_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean)
-/
@[path]
private lemma triangularFaceCoeff_ne_zero_of_cast_ne_zero_eq
  {a b : ZMod 2}
-- given
  (h : ((((a.val : Int) - (b.val : Int) : Int)) : ZMod 2) ≠ 0) :
-- imply
  (a.val : Int) - b.val ≠ 0 := by
-- proof
  apply StatMech.FrontierA.triangularFaceCoeff_ne_zero_of_cast_ne_zero a b h

/--
[triangularFaceEastCoeff_eq_zero_of_cast_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean)
-/
@[path]
private lemma triangularFaceEastCoeff_eq_zero_of_cast_eq_zero_eq
  {L : Nat}
  {p : ZMod L × ZMod L}
-- given
  (lower upper : (ZMod L × ZMod L) -> ZMod 2)
  (h : (triangularFaceEastCoeff lower upper p : ZMod 2) = 0) :
-- imply
  triangularFaceEastCoeff lower upper p = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFaceEastCoeff_eq_zero_of_cast_eq_zero lower upper p h

/--
[triangularFaceNorthCoeff_eq_zero_of_cast_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean)
-/
@[path]
private lemma triangularFaceNorthCoeff_eq_zero_of_cast_eq_zero_eq
  {L : Nat}
  {p : ZMod L × ZMod L}
-- given
  (lower upper : (ZMod L × ZMod L) -> ZMod 2)
  (h : (triangularFaceNorthCoeff lower upper p : ZMod 2) = 0) :
-- imply
  triangularFaceNorthCoeff lower upper p = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFaceNorthCoeff_eq_zero_of_cast_eq_zero lower upper p h

/--
[triangularFaceDiagonalCoeff_eq_zero_of_cast_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean)
-/
@[path]
private lemma triangularFaceDiagonalCoeff_eq_zero_of_cast_eq_zero_eq
  {L : Nat}
  {p : ZMod L × ZMod L}
-- given
  (lower upper : (ZMod L × ZMod L) -> ZMod 2)
  (h : (triangularFaceDiagonalCoeff lower upper p : ZMod 2) = 0) :
-- imply
  triangularFaceDiagonalCoeff lower upper p = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFaceDiagonalCoeff_eq_zero_of_cast_eq_zero lower upper p h

/--
[triangularFaceBoundary_horizontal_seam_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean)
-/
@[path]
private lemma triangularFaceBoundary_horizontal_seam_sum_eq
  {L : Nat}
  [NeZero L]
  {x : ZMod L}
-- given
  (lower upper : (ZMod L × ZMod L) -> ZMod 2) :
-- imply
  (∑ y : ZMod L, (triangularFaceEastCoeff lower upper (x, y) + triangularFaceDiagonalCoeff lower upper (x, y))) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFaceBoundary_horizontal_seam_sum lower upper x

/--
[triangularFaceBoundary_vertical_seam_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFaceBoundary.lean)
-/
@[path]
private lemma triangularFaceBoundary_vertical_seam_sum_eq
  {L : Nat}
  [NeZero L]
  {y : ZMod L}
-- given
  (lower upper : (ZMod L × ZMod L) -> ZMod 2) :
-- imply
  (∑ x : ZMod L, (triangularFaceNorthCoeff lower upper (x, y) + triangularFaceDiagonalCoeff lower upper (x, y))) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFaceBoundary_vertical_seam_sum lower upper y


-- created on 2026-10-23
