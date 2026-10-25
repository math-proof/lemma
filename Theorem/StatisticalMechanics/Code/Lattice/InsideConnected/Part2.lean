/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerSeparation.Part2
import Def.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem mem_offSupportComponent {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed z : Site 2} :
    z ∈ offSupportComponent Vc seed ↔ (offSupport Vc).Reachable seed z := Iff.rfl


theorem seed_mem_offSupportComponent {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (seed : Site 2) : seed ∈ offSupportComponent Vc seed :=
  SimpleGraph.Reachable.refl _


theorem offSupportComponent_subset_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∈ jec_leftRegion Vc) (hsoff : seed ∉ Vc.support) :
    offSupportComponent Vc seed ⊆ jec_leftRegion Vc := by
  intro z hz
  rw [mem_offSupportComponent] at hz
  exact offSupport_component_monochromatic Vc hseed hz hsoff


theorem offSupportComponent_subset_exterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ jec_leftRegion Vc) (hsoff : seed ∉ Vc.support) :
    offSupportComponent Vc seed ⊆ (jec_leftRegion Vc)ᶜ := by
  intro z hz
  rw [mem_offSupportComponent] at hz
  exact offSupport_component_monochromatic_out Vc hseed hz hsoff


theorem offSupportComponent_offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hsoff : seed ∉ Vc.support) {z : Site 2}
    (hz : z ∈ offSupportComponent Vc seed) : z ∉ Vc.support := by
  rw [mem_offSupportComponent] at hz
  obtain ⟨pw, hpw⟩ := offSupport_reachable_to_offSupportWalk Vc hz hsoff
  exact hpw z pw.end_mem_support


theorem offSupportComponent_hub {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (seed : Site 2) :
    ∀ z : Site 2, z ∈ offSupportComponent Vc seed → (offSupport Vc).Reachable seed z :=
  fun _ hz => (mem_offSupportComponent Vc).mp hz


theorem interior_eq_offSupportComponent_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∈ jec_leftRegion Vc) (hsoff : seed ∉ Vc.support) :
    jec_leftRegion Vc = offSupportComponent Vc seed ↔
      jec_leftRegion Vc ⊆ offSupportComponent Vc seed := by
  constructor
  · intro h; rw [h]
  · intro h
    exact le_antisymm h (offSupportComponent_subset_interior Vc hseed hsoff)


theorem interiorHub_of_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2}
    (hcov : jec_leftRegion Vc ⊆ offSupportComponent Vc seed) :
    ∀ s : Site 2, s ∈ jec_leftRegion Vc → (offSupport Vc).Reachable seed s :=
  fun _ hs => (mem_offSupportComponent Vc).mp (hcov hs)


theorem hInOff_of_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    {seed : Site 2}
    (hcov : jec_leftRegion Vc ⊆ offSupportComponent Vc seed) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support :=
  hInOff_of_interiorHub Vc hoff (interiorHub_of_covers Vc hcov)


theorem inside_offSupport_connected_of_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2}
    (hcov : jec_leftRegion Vc ⊆ offSupportComponent Vc seed) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      (offSupport Vc).Reachable s t := by
  intro s t hs ht
  exact ((interiorHub_of_covers Vc hcov s hs).symm).trans (interiorHub_of_covers Vc hcov t ht)


theorem cycle_boundedRegionCount_one {V : Type*} {G : SimpleGraph V} [Finite V] [DecidableEq V]
    {w : V} (c : G.Walk w w) (hc : c.IsCycle) :
    jes_boundedRegionCount c.toSubgraph.coe = 1 :=
  jes_cycle_boundedRegionCount_one c hc


theorem two_components_of_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    (hoffOut : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
    {sIn sOut : Site 2}
    (hcovIn : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn)
    (hcovOut : (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
  refine jlri_two_components_of_offSupport_connected Vc hp hq
    (hInOff_of_covers Vc hoffIn hcovIn) ?_
  intro s t hs ht
  have hubOut : ∀ r : Site 2, r ∉ jec_leftRegion Vc → (offSupport Vc).Reachable sOut r :=
    fun r hr => (mem_offSupportComponent Vc).mp (hcovOut hr)
  have hconn : (offSupport Vc).Reachable s t := ((hubOut s hs).symm).trans (hubOut t ht)
  exact offSupport_reachable_to_offSupportWalk Vc hconn (hoffOut _ hs)


theorem minimalLoop_offSupportComponent_subset_interior (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {seed : Site 2}
    (hseed : seed ∈ jec_leftRegion (mpl_orbitLoop K a))
    (hsoff : seed ∉ (mpl_orbitLoop K a).support) :
    offSupportComponent (mpl_orbitLoop K a) seed ⊆ jec_leftRegion (mpl_orbitLoop K a) :=
  offSupportComponent_subset_interior (mpl_orbitLoop K a) hseed hsoff


theorem minimalLoop_hInOff_of_covers (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hoff : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
    {seed : Site 2}
    (hcov : jec_leftRegion (mpl_orbitLoop K a) ⊆ offSupportComponent (mpl_orbitLoop K a) seed) :
    ∀ s t : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) →
      t ∈ jec_leftRegion (mpl_orbitLoop K a) →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ (mpl_orbitLoop K a).support :=
  hInOff_of_covers (mpl_orbitLoop K a) hoff hcov


theorem minimalLoop_two_components_of_covers (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p (mpl_orbitLoop K a)))
    (hq : ∀ w ∈ (mpl_orbitLoop K a).support, w 0 ≤ q 0 - 1)
    (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
    (hoffOut : ∀ s ∉ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
    {sIn sOut : Site 2}
    (hcovIn : jec_leftRegion (mpl_orbitLoop K a) ⊆ offSupportComponent (mpl_orbitLoop K a) sIn)
    (hcovOut : (jec_leftRegion (mpl_orbitLoop K a))ᶜ ⊆
        offSupportComponent (mpl_orbitLoop K a) sOut) :
    Nat.card (latticeMinusBarrier (jec_leftRegion (mpl_orbitLoop K a))).ConnectedComponent = 2 :=
  two_components_of_covers (mpl_orbitLoop K a) hp hq hoffIn hoffOut hcovIn hcovOut


theorem offSupport_reachable_symm {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (h : (offSupport Vc).Reachable x y) : (offSupport Vc).Reachable y x :=
  h.symm

theorem offSupport_reachable_trans {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y z : Site 2} (hxy : (offSupport Vc).Reachable x y) (hyz : (offSupport Vc).Reachable y z) :
    (offSupport Vc).Reachable x z :=
  hxy.trans hyz


theorem inside_offSupport_connected_iff_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∈ jec_leftRegion Vc) :
    (∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        (offSupport Vc).Reachable s t)
      ↔ jec_leftRegion Vc ⊆ offSupportComponent Vc seed := by
  constructor
  · intro hconn z hz
    exact (mem_offSupportComponent Vc).mpr (hconn seed z hseed hz)
  · intro hcov
    exact inside_offSupport_connected_of_covers Vc hcov


theorem hInOff_iff_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    {seed : Site 2} (hseed : seed ∈ jec_leftRegion Vc) :
    (∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
      ↔ jec_leftRegion Vc ⊆ offSupportComponent Vc seed := by
  constructor
  · intro hwalk z hz
    obtain ⟨pw, hpw⟩ := hwalk seed z hseed hz
    exact (mem_offSupportComponent Vc).mpr (offSupportWalk_to_offSupport_reachable Vc pw hpw)
  · intro hcov
    exact hInOff_of_covers Vc hoff hcov

end Lattice
end StatMech
