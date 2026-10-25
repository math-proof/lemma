import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.PeierlsArcAssembly.Part3
open Set SimpleGraph Function StatMech StatMech.Ising


/--
[paa_reach_a_or_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_reach_a_or_b_eq
  {G : SimpleGraph W}
  {a b : W}
  {s x : W}
  {p : G.Walk s x}
-- given
  (h : (G.deleteEdges {s(a, b)}).Reachable a s ∨ (G.deleteEdges {s(a, b)}).Reachable b s) :
-- imply
  ((G.deleteEdges {s(a, b)}).Reachable a x ∨ (G.deleteEdges {s(a, b)}).Reachable b x) := by
-- proof
  apply StatMech.Ising.paa_reach_a_or_b p h

/--
[paa_sup_edge_deleteEdges_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_sup_edge_deleteEdges_eq_eq
  {G : SimpleGraph W}
  {a b : W}
-- given
  (hnotin : s(a, b) ∉ G.edgeSet) :
-- imply
  (G ⊔ edge a b).deleteEdges {s(a, b)} = G := by
-- proof
  apply StatMech.Ising.paa_sup_edge_deleteEdges_eq hnotin

/--
[paa_two_components_count_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_two_components_count_sup_eq
  {G : SimpleGraph W}
  {a b : W}
-- given
  (hnotin : s(a, b) ∉ G.edgeSet)
  (hconn : (G ⊔ edge a b).Connected)
  (hbridge : ¬ G.Reachable a b) :
-- imply
  Nat.card G.ConnectedComponent = 2 := by
-- proof
  apply StatMech.Ising.paa_two_components_count_sup hnotin hconn hbridge

/--
[paa_two_components_of_arcNoSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_two_components_of_arcNoSeparation_eq
  {G : SimpleGraph W}
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {B' : Set (Sym2 V)}
  {a b : V}
-- given
  (h0 : paa_ArcNoSeparation A B')
  (he : s(a, b) ∈ (A.deleteEdges B').edgeSet)
  (h1 : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
-- imply
  Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Ising.paa_two_components_of_arcNoSeparation A B' h0 he h1

/--
[paa_bridge_of_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_bridge_of_separation_eq
  {G : SimpleGraph W}
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {B' : Set (Sym2 V)}
  {a b : V}
-- given
  (hsep : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
-- imply
  ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b := by
-- proof
  apply StatMech.Ising.paa_bridge_of_separation A B' hsep

/--
[paa_dualModel_of_arcNoSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_dualModel_of_arcNoSeparation_eq
  {G : SimpleGraph W}
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {B' : Set (Sym2 V)}
  {a b : V}
-- given
  (h0 : paa_ArcNoSeparation A B')
  (he : s(a, b) ∈ (A.deleteEdges B').edgeSet)
  (hsep : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
-- imply
  ecc_DualCutModel A B' a b := by
-- proof
  apply StatMech.Ising.paa_dualModel_of_arcNoSeparation A B' h0 he hsep

/--
[paa_two_components_of_dualModel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_two_components_of_dualModel_eq
  {G : SimpleGraph W}
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {B' : Set (Sym2 V)}
  {a b : V}
-- given
  (h0 : paa_ArcNoSeparation A B')
  (he : s(a, b) ∈ (A.deleteEdges B').edgeSet)
  (hsep : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
-- imply
  Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Ising.paa_two_components_of_dualModel A B' h0 he hsep

/--
[paa_iccCount_of_arcNoSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_iccCount_of_arcNoSeparation_eq
  {G : SimpleGraph W}
  [Empty.Finite V]
  [DecidableEq V]
  {Vc : (hypercubicLattice 2).Walk a a}
  {a' b' : {z : Site 2 // z ∉ Vc.support}}
-- given
  (h0 : paa_ArcNoSeparationOff Vc a' b')
  (hsep : ¬ (icc_offComplGraph Vc).Reachable a' b') :
-- imply
  Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Ising.paa_iccCount_of_arcNoSeparation Vc h0 hsep

/--
[paa_separation_of_seeds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_separation_of_seeds_eq
  {G : SimpleGraph W}
  [Empty.Finite V]
  [DecidableEq V]
  {Vc : (hypercubicLattice 2).Walk a a}
  {a' b' : {z : Site 2 // z ∉ Vc.support}}
-- given
  (hInMem : (a' : Site 2) ∈ jec_leftRegion Vc)
  (hOutMem : (b' : Site 2) ∉ jec_leftRegion Vc) :
-- imply
  ¬ (icc_offComplGraph Vc).Reachable a' b' := by
-- proof
  apply StatMech.Ising.paa_separation_of_seeds Vc hInMem hOutMem

/--
[paa_covers_of_arcNoSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_covers_of_arcNoSeparation_eq
  {G : SimpleGraph W}
  [Empty.Finite V]
  [DecidableEq V]
  {Vc : (hypercubicLattice 2).Walk a a}
  {sIn sOut : Site 2}
-- given
  (hInOff : sIn ∉ Vc.support)
  (hOutOff : sOut ∉ Vc.support)
  (h0 : paa_ArcNoSeparationOff Vc ⟨sIn, hInOff⟩ ⟨sOut, hOutOff⟩)
  (hInMem : sIn ∈ jec_leftRegion Vc)
  (hOutMem : sOut ∉ jec_leftRegion Vc)
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
-- imply
  jec_leftRegion Vc ⊆ offSupportComponent Vc sIn := by
-- proof
  apply StatMech.Ising.paa_covers_of_arcNoSeparation Vc hInOff hOutOff h0 hInMem hOutMem hoffIn

/--
[paa_hInOff_of_arcNoSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_hInOff_of_arcNoSeparation_eq
  {G : SimpleGraph W}
  [Empty.Finite V]
  [DecidableEq V]
  {Vc : (hypercubicLattice 2).Walk a a}
  {sIn sOut : Site 2}
-- given
  (hInOff : sIn ∉ Vc.support)
  (hOutOff : sOut ∉ Vc.support)
  (h0 : paa_ArcNoSeparationOff Vc ⟨sIn, hInOff⟩ ⟨sOut, hOutOff⟩)
  (hInMem : sIn ∈ jec_leftRegion Vc)
  (hOutMem : sOut ∉ jec_leftRegion Vc)
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Ising.paa_hInOff_of_arcNoSeparation Vc hInOff hOutOff h0 hInMem hOutMem hoffIn

/--
[paa_two_components_of_arcNoSeparation_jlri](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_two_components_of_arcNoSeparation_jlri_eq
  {G : SimpleGraph W}
  [Empty.Finite V]
  [DecidableEq V]
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {p q : Site 2}
  {sIn sOut : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hInOff : sIn ∉ Vc.support)
  (hOutOff : sOut ∉ Vc.support)
  (h0 : paa_ArcNoSeparationOff Vc ⟨sIn, hInOff⟩ ⟨sOut, hOutOff⟩)
  (hInMem : sIn ∈ jec_leftRegion Vc)
  (hOutMem : sOut ∉ jec_leftRegion Vc)
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hOut : oc_OutsideReachesExterior Vc R) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Ising.paa_two_components_of_arcNoSeparation_jlri Vc R hsupp hp hq hInOff hOutOff h0 hInMem hOutMem hoffIn hOut

/--
[paa_peierls_long_range_order_of_planarConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_peierls_long_range_order_of_planarConnectivity_eq
  {G : SimpleGraph W}
  [Empty.Finite V]
  [DecidableEq V]
-- given
  (hConn : ∀ n : ℕ, PlanarConnectivity n) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 := by
-- proof
  apply StatMech.Ising.paa_peierls_long_range_order_of_planarConnectivity hConn

/--
[paa_count_nonvacuous_hyps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_count_nonvacuous_hyps_eq
  {G : SimpleGraph W}
  [Empty.Finite V]
  [DecidableEq V] :
-- imply
  s((0 : Fin 2), 1) ∉ (⊥ : SimpleGraph (Fin 2)).edgeSet ∧ ((⊥ : SimpleGraph (Fin 2)) ⊔ edge 0 1).Connected ∧ ¬ (⊥ : SimpleGraph (Fin 2)).Reachable 0 1 := by
-- proof
  apply StatMech.Ising.paa_count_nonvacuous_hyps

/--
[paa_count_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean)
-/
@[path]
private lemma paa_count_nonvacuous_eq
  {G : SimpleGraph W}
  [Empty.Finite V]
  [DecidableEq V] :
-- imply
  Nat.card (⊥ : SimpleGraph (Fin 2)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Ising.paa_count_nonvacuous


-- created on 2026-10-23
