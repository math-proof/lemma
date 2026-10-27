import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulPrimalConfinement
open SimpleGraph StatMech StatMech.FrontierD


/--
[FKRectRefinedOpenWalkBlocksAlong.faithfulRoute_fst_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulPrimalConfinement.lean)
-/
@[path]
private lemma faithfulRoute_fst_bounds_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x y}
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
  {right : Nat}
  {d : FKRectIntegralSquareDart}
  {s : Int × Int}
-- given
  (h : FKRectRefinedOpenWalkBlocksAlong R F w p q l)
  (hsupport : ∀ v ∈ w.support, 1 ≤ v.1.val ∧ v.1.val ≤ right)
  (hpcol : p.1 = (x.1.val : Int))
  (hd : d ∈ l)
  (hs : s ∈ fkRectFaithfulShearDartRoute d) :
-- imply
  16 ≤ s.1 ∧ s.1 ≤ 16 * (right : Int) + 8 := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedOpenWalkBlocksAlong.faithfulRoute_fst_bounds R F h right hsupport hpcol hd hs

/--
[FKRectRefinedOpenWalkBlocksAlong.exists_faithfulShearWalk_fst_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulPrimalConfinement.lean)
-/
@[path]
private lemma exists_faithfulShearWalk_fst_bounds_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x y}
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
  {right : Nat}
-- given
  (halong : FKRectRefinedOpenWalkBlocksAlong R F w p q l)
  (hpath : FKRectIntegralSquareDartPath (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)) (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)) l)
  (hl : l ≠ [])
  (hsupport : ∀ v ∈ w.support, 1 ≤ v.1.val ∧ v.1.val ≤ right)
  (hpcol : p.1 = (x.1.val : Int)) :
-- imply
  ∃ V : (hypercubicLattice 2).Walk (fkRectFaithfulShearPoint (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) (fkRectFaithfulShearPoint (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q))), ∀ z ∈ V.support, 16 ≤ z 0 ∧ z 0 ≤ 16 * (right : Int) + 8 := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedOpenWalkBlocksAlong.exists_faithfulShearWalk_fst_bounds R F halong hpath hl right hsupport hpcol


-- created on 2026-10-23
