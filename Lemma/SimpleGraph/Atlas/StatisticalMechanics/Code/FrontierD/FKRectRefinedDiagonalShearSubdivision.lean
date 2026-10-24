import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectRefinedDiagonalShearSubdivision
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectIntegralSquareDart_axisStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDiagonalShearSubdivision.lean)
-/
@[path]
private lemma fkRectIntegralSquareDart_axisStep_eq
  {d : FKRectIntegralSquareDart} :
-- imply
  FKRectSquareAxisStep d.1 (fkRectIntegralSquareDartEnd d) := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDart_axisStep d

/--
[FKRectIntegralSquareDartPath.exists_diagonalShearWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDiagonalShearSubdivision.lean)
-/
@[path]
private lemma exists_diagonalShearWalk_eq
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectIntegralSquareDartPath p q l) :
-- imply
  ∃ V : (hypercubicLattice 2).Walk (fkRectDiagonalShearPoint p) (fkRectDiagonalShearPoint q), ∀ z ∈ V.support, z = fkRectDiagonalShearPoint p ∨ ∃ d ∈ l, z = fkRectDiagonalShearMidpoint d.1 (fkRectIntegralSquareDartEnd d) ∨ z = fkRectDiagonalShearPoint (fkRectIntegralSquareDartEnd d) := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.exists_diagonalShearWalk h

/--
[FKRectIntegralSquareDartPath.diagonalShearWalk_support_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDiagonalShearSubdivision.lean)
-/
@[path]
private lemma diagonalShearWalk_support_cases_eq
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
  {z : Site 2}
-- given
  (h : FKRectIntegralSquareDartPath p q l)
  (hz : z ∈ h.diagonalShearWalk.support) :
-- imply
  z = fkRectDiagonalShearPoint p ∨ ∃ d ∈ l, z = fkRectDiagonalShearMidpoint d.1 (fkRectIntegralSquareDartEnd d) ∨ z = fkRectDiagonalShearPoint (fkRectIntegralSquareDartEnd d) := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.diagonalShearWalk_support_cases h hz


-- created on 2026-10-23
