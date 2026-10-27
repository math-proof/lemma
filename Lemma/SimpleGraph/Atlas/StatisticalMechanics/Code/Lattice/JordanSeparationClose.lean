import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationClose.Part3
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[jsc_walk_col_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean)
-/
@[path]
private lemma jsc_walk_col_bound_eq
  {a b : Site 2}
  {Vc : (hypercubicLattice 2).Walk a b} :
-- imply
  ∃ M : ℤ, ∀ p ∈ Vc.support, p 0 ≤ M := by
-- proof
  apply StatMech.Lattice.jsc_walk_col_bound Vc

/--
[jsc_exists_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean)
-/
@[path]
private lemma jsc_exists_outside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  ∃ q : Site 2, q ∉ jec_leftRegion Vc ∧ ∀ p ∈ Vc.support, p 0 ≤ q 0 - 1 := by
-- proof
  apply StatMech.Lattice.jsc_exists_outside Vc

/--
[jsc_inside_not_reachable_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean)
-/
@[path]
private lemma jsc_inside_not_reachable_outside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hx : ¬ Even (jec_rayCount x Vc))
  (hy : Even (jec_rayCount y Vc)) :
-- imply
  ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
-- proof
  apply StatMech.Lattice.jsc_inside_not_reachable_outside Vc hx hy

/--
[jsc_side_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean)
-/
@[path]
private lemma jsc_side_constant_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (h : (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y) :
-- imply
  (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount y Vc)) := by
-- proof
  apply StatMech.Lattice.jsc_side_constant Vc h

/--
[jsc_two_components_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean)
-/
@[path]
private lemma jsc_two_components_of_connected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {p : Site 2}
-- given
  (hp : ¬ Even (jec_rayCount p Vc))
  (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t)
  (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jsc_two_components_of_connected Vc hp hin hout

/--
[jsc_separation_of_JordanSeparates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean)
-/
@[path]
private lemma jsc_separation_of_JordanSeparates_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : jsc_JordanSeparates Vc) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 ∧ (∃ q : Site 2, q ∉ jec_leftRegion Vc) ∧ (∀ x y : Site 2, ¬ Even (jec_rayCount x Vc) → Even (jec_rayCount y Vc) → ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y) := by
-- proof
  apply StatMech.Lattice.jsc_separation_of_JordanSeparates Vc h

/--
[jsc_cycle_faceCount_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean)
-/
@[path]
private lemma jsc_cycle_faceCount_eq_two_eq
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
-- given
  (hc : c.IsCycle) :
-- imply
  faceCount c.toSubgraph.coe = 2 := by
-- proof
  apply StatMech.Lattice.jsc_cycle_faceCount_eq_two c hc

/--
[jsc_cycle_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean)
-/
@[path]
private lemma jsc_cycle_separation_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hcyc : Vc.IsCycle)
  (hsep : jsc_JordanSeparates Vc) :
-- imply
  faceCount Vc.toSubgraph.coe = 2 ∧ Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jsc_cycle_separation Vc hcyc hsep

/--
[jsc_cluster_inside_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean)
-/
@[path]
private lemma jsc_cluster_inside_connected_eq
  {o : Site 2}
  {x y : Site 2}
-- given
  (hx : x ∈ cluster 2 ω o)
  (hy : y ∈ cluster 2 ω o) :
-- imply
  (latticeMinusBarrier (cluster 2 ω o)).Reachable x y := by
-- proof
  apply StatMech.Lattice.jsc_cluster_inside_connected o hx hy

/--
[jsc_separation_of_loopBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean)
-/
@[path]
private lemma jsc_separation_of_loopBridge_eq
  {o : Site 2}
-- given
  (hfin : (cluster 2 ω o).Finite)
  (hloop : ccs_OrbitIsLoop (cluster 2 ω o))
  (hout : ∀ s t : Site 2, s ∉ cluster 2 ω o → t ∉ cluster 2 ω o → (latticeMinusBarrier (cluster 2 ω o)).Reachable s t) :
-- imply
  Nat.card (latticeMinusBarrier (cluster 2 ω o)).ConnectedComponent = 2 ∧ ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), cluster 2 ω o = jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.jsc_separation_of_loopBridge o hfin hloop hout

/--
[jsc_unitSquareLoop_inside_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean)
-/
@[path]
private lemma jsc_unitSquareLoop_inside_odd_eq :
-- imply
  ¬ Even (jec_rayCount (![1, 1] : Site 2) jsc_unitSquareLoop) := by
-- proof
  apply StatMech.Lattice.jsc_unitSquareLoop_inside_odd

/--
[jsc_JordanSeparates_inside_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean)
-/
@[path]
private lemma jsc_JordanSeparates_inside_satisfiable_eq :
-- imply
  ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), ∃ p, ¬ Even (jec_rayCount p Vc) := by
-- proof
  apply StatMech.Lattice.jsc_JordanSeparates_inside_satisfiable


-- created on 2026-10-23
