import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusPlusBoundaryField.Part2
open Finset StatMech StatMech.FrontierA


/--
[mk_mem_plusBoundaryEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusPlusBoundaryField.lean)
-/
@[path]
private lemma mk_mem_plusBoundaryEdges_iff_eq
  {d k R : Nat}
  {S : Finset (Site d)}
  {a b : Site d} :
-- imply
  s(a, b) ∈ plusBoundaryEdges S ↔ (hypercubicLattice d).Adj a b ∧ ((a ∈ S ∧ b ∉ S) ∨ (a ∉ S ∧ b ∈ S)) := by
-- proof
  apply StatMech.FrontierA.mk_mem_plusBoundaryEdges_iff S a b

/--
[exists_latticeNeighbor_lift_of_torusAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusPlusBoundaryField.lean)
-/
@[path]
private lemma exists_latticeNeighbor_lift_of_torusAdj_eq
  {d k R : Nat}
  {x : Site d}
  {z : IsingDyadicTorus d k}
-- given
  (h : (isingTorusGraph d k).Adj (isingSiteToDyadicTorus k x) z) :
-- imply
  ∃ y : Site d, (hypercubicLattice d).Adj x y ∧ isingSiteToDyadicTorus k y = z := by
-- proof
  apply StatMech.FrontierA.exists_latticeNeighbor_lift_of_torusAdj x z h

/--
[latticeNeighborLiftOfTorusAdj_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusPlusBoundaryField.lean)
-/
@[path]
private lemma latticeNeighborLiftOfTorusAdj_spec_eq
  {d k R : Nat}
  {x : Site d}
  {z : IsingDyadicTorus d k}
-- given
  (h : (isingTorusGraph d k).Adj (isingSiteToDyadicTorus k x) z) :
-- imply
  (hypercubicLattice d).Adj x (latticeNeighborLiftOfTorusAdj x z h) ∧ isingSiteToDyadicTorus k (latticeNeighborLiftOfTorusAdj x z h) = z := by
-- proof
  apply StatMech.FrontierA.latticeNeighborLiftOfTorusAdj_spec x z h

/--
[finiteCutPlusBoundaryField_isingTorusImageEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusPlusBoundaryField.lean)
-/
@[path]
private lemma finiteCutPlusBoundaryField_isingTorusImageEquiv_eq
  {d k R : Nat}
  {S : Finset (Site d)}
-- given
  (hS : (↑S : Set (Site d)) ⊆ box d R)
  (hside : 2 * (R + 1) < isingDyadicSide k)
  (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)))
  (x : {x // x ∈ S}) :
-- imply
  finiteCutPlusBoundaryField (isingTorusGraph d k) (isingTorusImageFinset k S) (isingTorusImageEquiv S hinj x) = plusBoundaryField S x := by
-- proof
  apply StatMech.FrontierA.finiteCutPlusBoundaryField_isingTorusImageEquiv S hS hside hinj x


-- created on 2026-10-23
