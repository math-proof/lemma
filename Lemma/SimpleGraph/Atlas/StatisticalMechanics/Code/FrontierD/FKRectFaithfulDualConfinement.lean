import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulDualConfinement
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectFaithfulShearPoint_refinedDualScale_develop_fst_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulDualConfinement.lean)
-/
@[path]
private lemma fkRectFaithfulShearPoint_refinedDualScale_develop_fst_bounds_eq
  {p : Int × Int}
  {right : Nat}
-- given
  (hleft : 0 <= p.1)
  (hright : p.1 <= right) :
-- imply
  8 <= (fkRectFaithfulShearPoint (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p))) 0 ∧ (fkRectFaithfulShearPoint (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p))) 0 <= 16 * (right : Int) + 16 := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearPoint_refinedDualScale_develop_fst_bounds p right hleft hright

/--
[FKRectRefinedDualOpenWalkBlocksAlong.faithfulRoute_fst_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulDualConfinement.lean)
-/
@[path]
private lemma faithfulRoute_fst_bounds_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Walk x y}
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
  {right : Nat}
  {d : FKRectIntegralSquareDart}
  {r : Int × Int}
-- given
  (h : FKRectRefinedDualOpenWalkBlocksAlong R omega w p q l)
  (hproper : right + 1 < R.width)
  (hsupport : ∀ v ∈ w.support, v.1.val <= right)
  (hpcol : p.1 = (x.1.val : Int))
  (hd : d ∈ l)
  (hr : r ∈ fkRectFaithfulShearDartRoute d) :
-- imply
  8 <= r.1 ∧ r.1 <= 16 * (right : Int) + 16 := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedDualOpenWalkBlocksAlong.faithfulRoute_fst_bounds R omega h right hproper hsupport hpcol hd hr

/--
[exists_fkRectRefinedDualOpenWalkFaithfulShear_fst_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulDualConfinement.lean)
-/
@[path]
private lemma exists_fkRectRefinedDualOpenWalkFaithfulShear_fst_bounds_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Walk x y}
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
  {right : Nat}
-- given
  (hpath : FKRectIntegralSquareDartPath (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)) (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint q)) l)
  (halong : FKRectRefinedDualOpenWalkBlocksAlong R omega w p q l)
  (hlne : l ≠ [])
  (hproper : right + 1 < R.width)
  (hsupport : ∀ v ∈ w.support, v.1.val <= right)
  (hpcol : p.1 = (x.1.val : Int)) :
-- imply
  ∃ W : (hypercubicLattice 2).Walk (fkRectFaithfulShearPoint (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p))) (fkRectFaithfulShearPoint (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint q))), ∀ z ∈ W.support, 8 <= z 0 ∧ z 0 <= 16 * (right : Int) + 16 := by
-- proof
  apply StatMech.FrontierD.exists_fkRectRefinedDualOpenWalkFaithfulShear_fst_bounds R omega hpath halong hlne right hproper hsupport hpcol


-- created on 2026-10-23
