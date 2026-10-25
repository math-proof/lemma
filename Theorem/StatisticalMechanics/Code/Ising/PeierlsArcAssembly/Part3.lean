/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsArcAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InsideCoveringClose
import Theorem.StatisticalMechanics.Code.Ising.PeierlsPlanarAssembly
import Def.StatisticalMechanics.Code.Ising.PeierlsArcAssembly.Part2
open Set SimpleGraph Function


set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice


variable {W : Type*} {G : SimpleGraph W}


variable {V : Type*} [Finite V] [DecidableEq V]


theorem paa_iccCount_of_arcNoSeparation (Vc : (hypercubicLattice 2).Walk a a)
    {a' b' : {z : Site 2 // z ∉ Vc.support}}
    (h1 : paa_ArcNoSeparationOff Vc a' b')
    (hsep : ¬ (icc_offComplGraph Vc).Reachable a' b') :
    Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2 :=
  paa_two_components_count_sup h1.1 h1.2 hsep


theorem paa_separation_of_seeds (Vc : (hypercubicLattice 2).Walk a a)
    {a' b' : {z : Site 2 // z ∉ Vc.support}}
    (hInMem : (a' : Site 2) ∈ jec_leftRegion Vc) (hOutMem : (b' : Site 2) ∉ jec_leftRegion Vc) :
    ¬ (icc_offComplGraph Vc).Reachable a' b' := by
  intro hreach
  have hne : (icc_offComplGraph Vc).connectedComponentMk a' ≠
      (icc_offComplGraph Vc).connectedComponentMk b' :=
    icc_components_distinct Vc hInMem hOutMem
  exact hne (ConnectedComponent.eq.mpr hreach)


theorem paa_covers_of_arcNoSeparation (Vc : (hypercubicLattice 2).Walk a a)
    {sIn sOut : Site 2} (hInOff : sIn ∉ Vc.support) (hOutOff : sOut ∉ Vc.support)
    (h1 : paa_ArcNoSeparationOff Vc ⟨sIn, hInOff⟩ ⟨sOut, hOutOff⟩)
    (hInMem : sIn ∈ jec_leftRegion Vc) (hOutMem : sOut ∉ jec_leftRegion Vc)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
    jec_leftRegion Vc ⊆ offSupportComponent Vc sIn :=
  icc_covers_of_two_components Vc
    (paa_iccCount_of_arcNoSeparation Vc h1 (paa_separation_of_seeds Vc hInMem hOutMem))
    hInMem hInOff hOutMem hOutOff hoffIn


theorem paa_hInOff_of_arcNoSeparation (Vc : (hypercubicLattice 2).Walk a a)
    {sIn sOut : Site 2} (hInOff : sIn ∉ Vc.support) (hOutOff : sOut ∉ Vc.support)
    (h1 : paa_ArcNoSeparationOff Vc ⟨sIn, hInOff⟩ ⟨sOut, hOutOff⟩)
    (hInMem : sIn ∈ jec_leftRegion Vc) (hOutMem : sOut ∉ jec_leftRegion Vc)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support :=
  icc_hInOff_of_two_components Vc
    (paa_iccCount_of_arcNoSeparation Vc h1 (paa_separation_of_seeds Vc hInMem hOutMem))
    hInMem hInOff hOutMem hOutOff hoffIn


theorem paa_two_components_of_arcNoSeparation_jlri (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    {sIn sOut : Site 2} (hInOff : sIn ∉ Vc.support) (hOutOff : sOut ∉ Vc.support)
    (h1 : paa_ArcNoSeparationOff Vc ⟨sIn, hInOff⟩ ⟨sOut, hOutOff⟩)
    (hInMem : sIn ∈ jec_leftRegion Vc) (hOutMem : sOut ∉ jec_leftRegion Vc)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    (hOut : oc_OutsideReachesExterior Vc R) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  icc_two_components_of_count Vc R hsupp hp hq
    (paa_iccCount_of_arcNoSeparation Vc h1 (paa_separation_of_seeds Vc hInMem hOutMem))
    hInMem hInOff hOutMem hOutOff hoffIn hOut


theorem paa_peierls_long_range_order_of_planarConnectivity
    (hConn : ∀ n : ℕ, PlanarConnectivity n) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 :=
  peierls_long_range_order_of_planarConnectivity hConn


theorem paa_count_nonvacuous_hyps :
    s((0 : Fin 2), 1) ∉ (⊥ : SimpleGraph (Fin 2)).edgeSet ∧
      ((⊥ : SimpleGraph (Fin 2)) ⊔ edge 0 1).Connected ∧
      ¬ (⊥ : SimpleGraph (Fin 2)).Reachable 0 1 := by
  refine ⟨by decide, ?_, by decide⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · exact Reachable.refl _
  · refine Adj.reachable ?_
    rw [sup_adj]; right; rw [edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, by decide⟩


theorem paa_count_nonvacuous :
    Nat.card (⊥ : SimpleGraph (Fin 2)).ConnectedComponent = 2 := by
  obtain ⟨hnotin, hconn, hbridge⟩ := paa_count_nonvacuous_hyps
  exact paa_two_components_count_sup hnotin hconn hbridge

end Ising
end StatMech
