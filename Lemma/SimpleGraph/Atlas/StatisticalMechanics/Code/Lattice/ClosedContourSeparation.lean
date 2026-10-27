import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[ccs_closedLoop_leftRegion_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_closedLoop_leftRegion_bdEdge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.ccs_closedLoop_leftRegion_bdEdge Vc hadj hbd

/--
[ccs_closedLoop_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_closedLoop_inside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (h : ¬ Even (jec_rayCount z Vc)) :
-- imply
  z ∈ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.ccs_closedLoop_inside Vc h

/--
[ccs_closedLoop_outside_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_closedLoop_outside_far_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ Vc.support, p 0 ≤ z 0 - 1) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.ccs_closedLoop_outside_far Vc hfar

/--
[ccs_closedLoop_outside_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_closedLoop_outside_left_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hleft : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.ccs_closedLoop_outside_left Vc hleft

/--
[ccs_closedLoop_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_closedLoop_separation_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {inside outside : Set (Site 2)}
-- given
  (hin : ∀ z ∈ inside, ¬ Even (jec_rayCount z Vc))
  (hout : ∀ z ∈ outside, Even (jec_rayCount z Vc)) :
-- imply
  jcu_HasSeparatingSide Set.univ {z | z ∈ Vc.support} inside outside := by
-- proof
  apply StatMech.Lattice.ccs_closedLoop_separation Vc inside outside hin hout

/--
[ccs_closedLoop_separatingSide_forces_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_closedLoop_separatingSide_forces_cross_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {inside outside : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hin : ∀ z ∈ inside, ¬ Even (jec_rayCount z Vc))
  (hout : ∀ z ∈ outside, Even (jec_rayCount z Vc))
  (hx : x ∈ inside)
  (hy : y ∈ outside) :
-- imply
  ∃ z ∈ w.support, z ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.ccs_closedLoop_separatingSide_forces_cross Vc inside outside hin hout hx hy w

/--
[ccs_closedLoop_hasSeparatingSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_closedLoop_hasSeparatingSide_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {p q : Site 2}
-- given
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1) :
-- imply
  jcu_HasSeparatingSide Set.univ {z | z ∈ Vc.support} {p} {q} := by
-- proof
  apply StatMech.Lattice.ccs_closedLoop_hasSeparatingSide Vc hp hq

/--
[ccs_closedLoop_two_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_closedLoop_two_components_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {p q : Site 2}
-- given
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t)
  (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.ccs_closedLoop_two_components Vc hp hq hin hout

/--
[ccs_clusterSeparatingSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_clusterSeparatingSide_eq
  {K : Set (Site 2)}
-- given
  (h : ccs_OrbitIsLoop K) :
-- imply
  ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), jcu_HasSeparatingSide Set.univ {z | z ∈ Vc.support} K Kᶜ := by
-- proof
  apply StatMech.Lattice.ccs_clusterSeparatingSide h

/--
[ccs_cluster_forces_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_cluster_forces_cross_eq
  {K : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : ccs_OrbitIsLoop K)
  (hx : x ∈ K)
  (hy : y ∉ K) :
-- imply
  ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), (∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc)) ∧ (∀ z, z ∉ K → Even (jec_rayCount z Vc)) ∧ ∃ z ∈ w.support, z ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.ccs_cluster_forces_cross h hx hy w

/--
[ccs_cluster_eq_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_cluster_eq_leftRegion_eq
  {K : Set (Site 2)}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc))
  (hout : ∀ z, z ∉ K → Even (jec_rayCount z Vc)) :
-- imply
  K = jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.ccs_cluster_eq_leftRegion Vc hin hout

/--
[ccs_cluster_two_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_cluster_two_components_eq
  {K : Set (Site 2)}
  {p q : Site 2}
-- given
  (h : ccs_OrbitIsLoop K)
  (hp : p ∈ K)
  (hq : q ∉ K)
  (hin : ∀ s t : Site 2, s ∈ K → t ∈ K → (latticeMinusBarrier K).Reachable s t)
  (hout : ∀ s t : Site 2, s ∉ K → t ∉ K → (latticeMinusBarrier K).Reachable s t) :
-- imply
  Nat.card (latticeMinusBarrier K).ConnectedComponent = 2 ∧ ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), K = jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.ccs_cluster_two_components h hp hq hin hout

/--
[ccs_pcSeparation_discharged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_pcSeparation_discharged_eq
-- given
  (hloop : ∀ (ω : ConfigSpace (Sym2 (Site 2))), (cluster 2 ω (origin 2)).Finite → ccs_OrbitIsLoop (cluster 2 ω (origin 2))) :
-- imply
  ∀ (ω : ConfigSpace (Sym2 (Site 2))), (cluster 2 ω (origin 2)).Finite → ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), jcu_HasSeparatingSide Set.univ {z | z ∈ Vc.support} (cluster 2 ω (origin 2)) (cluster 2 ω (origin 2))ᶜ := by
-- proof
  apply StatMech.Lattice.ccs_pcSeparation_discharged hloop

/--
[ccs_pc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_pc_lt_one_eq
-- given
  (hJordan : StatMech.Percolation.DiscreteJordanSeparation)
  (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), StatMech.Lattice.ExitDartsSameOrbit ω hfin) :
-- imply
  StatMech.Percolation.pc 2 < 1 := by
-- proof
  apply StatMech.Lattice.ccs_pc_lt_one hJordan hsame

/--
[ccs_pc_pos_and_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean)
-/
@[path]
private lemma ccs_pc_pos_and_lt_one_eq
-- given
  (hJordan : StatMech.Percolation.DiscreteJordanSeparation)
  (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), StatMech.Lattice.ExitDartsSameOrbit ω hfin) :
-- imply
  0 < StatMech.Percolation.pc 2 ∧ StatMech.Percolation.pc 2 < 1 := by
-- proof
  apply StatMech.Lattice.ccs_pc_pos_and_lt_one hJordan hsame


-- created on 2026-10-23
