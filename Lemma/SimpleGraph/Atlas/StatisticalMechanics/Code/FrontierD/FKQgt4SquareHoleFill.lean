import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareHoleFill.Part2
open Set SimpleGraph StatMech StatMech.FrontierD


/--
[squareHoleFillRadius_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareHoleFill.lean)
-/
@[path]
private lemma squareHoleFillRadius_spec_eq
  {S : Set (Site 2)}
-- given
  (hS : S.Finite) :
-- imply
  S ⊆ box 2 (squareHoleFillRadius S hS) := by
-- proof
  apply StatMech.FrontierD.squareHoleFillRadius_spec S hS

/--
[squareHoleFill_beacon_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareHoleFill.lean)
-/
@[path]
private lemma squareHoleFill_beacon_not_mem_eq
  {S : Set (Site 2)}
-- given
  (hS : S.Finite) :
-- imply
  beacon 2 (squareHoleFillRadius S hS) ∉ S := by
-- proof
  apply StatMech.FrontierD.squareHoleFill_beacon_not_mem S hS

/--
[subset_squareHoleFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareHoleFill.lean)
-/
@[path]
private lemma subset_squareHoleFill_eq
  {S : Set (Site 2)}
-- given
  (hS : S.Finite) :
-- imply
  S ⊆ squareHoleFill S hS := by
-- proof
  apply StatMech.FrontierD.subset_squareHoleFill S hS

/--
[squareHoleFill_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareHoleFill.lean)
-/
@[path]
private lemma squareHoleFill_subset_box_eq
  {S : Set (Site 2)}
-- given
  (hS : S.Finite) :
-- imply
  squareHoleFill S hS ⊆ box 2 (squareHoleFillRadius S hS) := by
-- proof
  apply StatMech.FrontierD.squareHoleFill_subset_box S hS

/--
[squareHoleFill_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareHoleFill.lean)
-/
@[path]
private lemma squareHoleFill_finite_eq
  {S : Set (Site 2)}
-- given
  (hS : S.Finite) :
-- imply
  (squareHoleFill S hS).Finite := by
-- proof
  apply StatMech.FrontierD.squareHoleFill_finite S hS

/--
[squareHoleFill_reaches_original](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareHoleFill.lean)
-/
@[path]
private lemma squareHoleFill_reaches_original_eq
  {S : Set (Site 2)}
  {x : Site 2}
-- given
  (hS : S.Finite)
  (hne : S.Nonempty)
  (hx : x ∈ squareHoleFill S hS) :
-- imply
  ∃ s ∈ S, (latticeMinusBarrier (squareHoleFill S hS)).Reachable x s := by
-- proof
  apply StatMech.FrontierD.squareHoleFill_reaches_original S hS hne hx

/--
[squareHoleFill_inside_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareHoleFill.lean)
-/
@[path]
private lemma squareHoleFill_inside_connected_eq
  {S : Set (Site 2)}
-- given
  (hS : S.Finite)
  (hne : S.Nonempty)
  (hconn : ∀ a b : S, ((hypercubicLattice 2).induce S).Reachable a b) :
-- imply
  ∀ a b : Site 2, a ∈ squareHoleFill S hS → b ∈ squareHoleFill S hS → (latticeMinusBarrier (squareHoleFill S hS)).Reachable a b := by
-- proof
  apply StatMech.FrontierD.squareHoleFill_inside_connected S hS hne hconn

/--
[squareHoleFill_outside_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareHoleFill.lean)
-/
@[path]
private lemma squareHoleFill_outside_connected_eq
  {S : Set (Site 2)}
-- given
  (hS : S.Finite) :
-- imply
  ∀ a b : Site 2, a ∉ squareHoleFill S hS → b ∉ squareHoleFill S hS → (latticeMinusBarrier (squareHoleFill S hS)).Reachable a b := by
-- proof
  apply StatMech.FrontierD.squareHoleFill_outside_connected S hS

/--
[squareHoleFill_faceBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareHoleFill.lean)
-/
@[path]
private lemma squareHoleFill_faceBoundaryConnected_eq
  {S : Set (Site 2)}
-- given
  (hS : S.Finite)
  (hne : S.Nonempty)
  (hconn : ∀ a b : S, ((hypercubicLattice 2).induce S).Reachable a b) :
-- imply
  FaceBoundaryConnected (squareHoleFill S hS) (phb_boundarySupport (squareHoleFill S hS) (squareHoleFill_finite S hS)) := by
-- proof
  apply StatMech.FrontierD.squareHoleFill_faceBoundaryConnected S hS hne hconn

/--
[squareHoleFill_faceBoundary_degree_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareHoleFill.lean)
-/
@[path]
private lemma squareHoleFill_faceBoundary_degree_eq_two_eq
  {S : Set (Site 2)}
  {f : Site 2}
-- given
  (hS : S.Finite)
  (hne : S.Nonempty)
  (hconn : ∀ a b : S, ((hypercubicLattice 2).induce S).Reachable a b)
  (hf : f ∈ (faceBoundaryGraph (squareHoleFill S hS)).support) :
-- imply
  (faceBoundaryGraph (squareHoleFill S hS)).degree f = 2 := by
-- proof
  apply StatMech.FrontierD.squareHoleFill_faceBoundary_degree_eq_two S hS hne hconn hf


-- created on 2026-10-23
