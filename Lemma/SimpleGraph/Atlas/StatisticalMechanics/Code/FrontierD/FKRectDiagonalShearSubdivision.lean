import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDiagonalShearSubdivision.Part2
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectDiagonalShearPoint_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean)
-/
@[path]
private lemma fkRectDiagonalShearPoint_add_eq
  {p u : Int × Int} :
-- imply
  fkRectDiagonalShearPoint (p.1 + u.1, p.2 + u.2) = ![(fkRectDiagonalShearPoint p) 0 + u.1 + u.2, (fkRectDiagonalShearPoint p) 1 + u.1 - u.2] := by
-- proof
  apply StatMech.FrontierD.fkRectDiagonalShearPoint_add p u

/--
[fkRectDiagonalShearPoint_develop_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean)
-/
@[path]
private lemma fkRectDiagonalShearPoint_develop_snd_eq
  {p : Int × Int} :
-- imply
  (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 1 = p.2 := by
-- proof
  apply StatMech.FrontierD.fkRectDiagonalShearPoint_develop_snd p

/--
[fkRectDiagonalShearPoint_develop_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean)
-/
@[path]
private lemma fkRectDiagonalShearPoint_develop_fst_eq
  {p : Int × Int} :
-- imply
  (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 0 = 2 * p.1 + (p.2 + 1) / 2 - p.2 / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectDiagonalShearPoint_develop_fst p

/--
[fkRectDiagonalShearPoint_develop_add_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean)
-/
@[path]
private lemma fkRectDiagonalShearPoint_develop_add_period_eq
  {R : FKRectTorus}
  {p u : Int × Int} :
-- imply
  fkRectDiagonalShearPoint (fkRectSquareDevelopPoint (p.1 + (R.width : Int) * u.1, p.2 + (R.height : Int) * u.2)) = ![(fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 0 + 2 * (R.width : Int) * u.1, (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 1 + (R.height : Int) * u.2] := by
-- proof
  apply StatMech.FrontierD.fkRectDiagonalShearPoint_develop_add_period R p u

/--
[FKRectSquareWalkLift.closed_diagonalShearPoint_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean)
-/
@[path]
private lemma closed_diagonalShearPoint_end_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {w : G.Walk x x}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  fkRectDiagonalShearPoint (fkRectSquareDevelopPoint q) = ![(fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 0 + 2 * (R.width : Int) * (fkRectWalkWinding R w).1, (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 1 + (R.height : Int) * (fkRectWalkWinding R w).2] := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.closed_diagonalShearPoint_end R h

/--
[FKRectSquareWalkLift.closed_diagonalShearPoint_end_of_verticalOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean)
-/
@[path]
private lemma closed_diagonalShearPoint_end_of_verticalOne_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {w : G.Walk x x}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q)
  (hw : fkRectWalkWinding R w = (0, 1)) :
-- imply
  fkRectDiagonalShearPoint (fkRectSquareDevelopPoint q) = ![(fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 0, (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 1 + (R.height : Int)] := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.closed_diagonalShearPoint_end_of_verticalOne R h hw

/--
[FKRectSquareWalkLift.end_fst_eq_val_of_support_positiveColumnBand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean)
-/
@[path]
private lemma end_fst_eq_val_of_support_positiveColumnBand_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x y}
  {p q : Int × Int}
  {right : Nat}
-- given
  (h : FKRectSquareWalkLift R w p q)
  (hsupport : ∀ v ∈ w.support, 1 ≤ v.1.val ∧ v.1.val ≤ right)
  (hp : p.1 = (x.1.val : Int)) :
-- imply
  q.1 = (y.1.val : Int) := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.end_fst_eq_val_of_support_positiveColumnBand R h right hsupport hp

/--
[fkRectDiagonalShearPoint_midpoint_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean)
-/
@[path]
private lemma fkRectDiagonalShearPoint_midpoint_adj_eq
  {p q : Int × Int}
-- given
  (h : FKRectSquareAxisStep p q) :
-- imply
  (hypercubicLattice 2).Adj (fkRectDiagonalShearPoint p) (fkRectDiagonalShearMidpoint p q) := by
-- proof
  apply StatMech.FrontierD.fkRectDiagonalShearPoint_midpoint_adj h

/--
[fkRectDiagonalShearMidpoint_point_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean)
-/
@[path]
private lemma fkRectDiagonalShearMidpoint_point_adj_eq
  {p q : Int × Int}
-- given
  (h : FKRectSquareAxisStep p q) :
-- imply
  (hypercubicLattice 2).Adj (fkRectDiagonalShearMidpoint p q) (fkRectDiagonalShearPoint q) := by
-- proof
  apply StatMech.FrontierD.fkRectDiagonalShearMidpoint_point_adj h

/--
[FKRectSquareWalkLift.exists_diagonalShearWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean)
-/
@[path]
private lemma exists_diagonalShearWalk_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x y}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  ∃ V : (hypercubicLattice 2).Walk (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint q)), ∀ z ∈ V.support, (∃ a ∈ w.support, ∃ u : Int × Int, fkRectLiftedVertex R u = a ∧ z = fkRectDiagonalShearPoint (fkRectSquareDevelopPoint u)) ∨ ∃ a b, s(a, b) ∈ w.edges ∧ ∃ u v : Int × Int, fkRectLiftedVertex R u = a ∧ fkRectLiftedVertex R v = b ∧ z = fkRectDiagonalShearMidpoint (fkRectSquareDevelopPoint u) (fkRectSquareDevelopPoint v) := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.exists_diagonalShearWalk R h

/--
[FKRectSquareWalkLift.diagonalShearWalk_support_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalShearSubdivision.lean)
-/
@[path]
private lemma diagonalShearWalk_support_cases_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x y}
  {p q : Int × Int}
  {z : Site 2}
-- given
  (h : FKRectSquareWalkLift R w p q)
  (hz : z ∈ (h.diagonalShearWalk R).support) :
-- imply
  (∃ a ∈ w.support, ∃ u : Int × Int, fkRectLiftedVertex R u = a ∧ z = fkRectDiagonalShearPoint (fkRectSquareDevelopPoint u)) ∨ ∃ a b, s(a, b) ∈ w.edges ∧ ∃ u v : Int × Int, fkRectLiftedVertex R u = a ∧ fkRectLiftedVertex R v = b ∧ z = fkRectDiagonalShearMidpoint (fkRectSquareDevelopPoint u) (fkRectSquareDevelopPoint v) := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.diagonalShearWalk_support_cases R h hz


-- created on 2026-10-23
