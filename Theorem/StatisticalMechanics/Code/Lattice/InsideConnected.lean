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
import Def.StatisticalMechanics.Code.Lattice.InsideConnected
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem offSupport_adj {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (x y : Site 2) :
    (offSupport Vc).Adj x y ↔
      (hypercubicLattice 2).Adj x y ∧ x ∉ Vc.support ∧ y ∉ Vc.support := Iff.rfl


theorem offSupport_le {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    offSupport Vc ≤ hypercubicLattice 2 := fun _ _ h => h.1


theorem offSupport_walk_support_offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (offSupport Vc).Walk x y) (hx : x ∉ Vc.support) :
    ∀ z ∈ p.support, z ∉ Vc.support := by
  induction p with
  | nil => intro z hz; rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
           exact hz ▸ hx
  | @cons u w c hadj q ih =>
    have hw : w ∉ Vc.support := hadj.2.2
    intro z hz
    rw [SimpleGraph.Walk.support_cons] at hz
    rcases List.mem_cons.mp hz with h | h
    · exact h ▸ hx
    · exact ih hw z h


theorem offSupport_to_offSupportWalk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (offSupport Vc).Walk x y) (hx : x ∉ Vc.support) :
    ∃ pw : (hypercubicLattice 2).Walk x y, ∀ z ∈ pw.support, z ∉ Vc.support := by
  refine ⟨p.mapLe (offSupport_le Vc), ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hz
  exact offSupport_walk_support_offSupport Vc p hx z hz


theorem offSupport_reachable_to_offSupportWalk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (h : (offSupport Vc).Reachable x y) (hx : x ∉ Vc.support) :
    ∃ pw : (hypercubicLattice 2).Walk x y, ∀ z ∈ pw.support, z ∉ Vc.support := by
  obtain ⟨p⟩ := h
  exact offSupport_to_offSupportWalk Vc p hx


theorem offSupportWalk_to_offSupport_reachable {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (p : (hypercubicLattice 2).Walk x y)
    (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
    (offSupport Vc).Reachable x y := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u w c hadj q ih =>
    have hu : u ∉ Vc.support := hp u (by simp)
    have hw : w ∉ Vc.support := hp w (by simp [SimpleGraph.Walk.support_cons])
    have htail : ∀ z ∈ q.support, z ∉ Vc.support := by
      intro z hz
      exact hp z (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
    have hadj' : (offSupport Vc).Adj u w := ⟨hadj, hu, hw⟩
    exact hadj'.reachable.trans (ih htail)


theorem offSupport_reachable_iff_offSupportWalk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : x ∉ Vc.support) :
    (offSupport Vc).Reachable x y ↔
      ∃ pw : (hypercubicLattice 2).Walk x y, ∀ z ∈ pw.support, z ∉ Vc.support := by
  constructor
  · intro h; exact offSupport_reachable_to_offSupportWalk Vc h hx
  · rintro ⟨pw, hpw⟩; exact offSupportWalk_to_offSupport_reachable Vc pw hpw


theorem inside_sameRegion_offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (h : (offSupport Vc).Reachable x y) (hx : x ∉ Vc.support) :
    (x ∈ jec_leftRegion Vc ↔ y ∈ jec_leftRegion Vc) := by
  obtain ⟨pw, hpw⟩ := offSupport_reachable_to_offSupportWalk Vc h hx
  exact jlri_sameRegion_along_offSupport_walk Vc pw hpw


theorem offSupport_component_monochromatic {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {s t : Site 2} (hs : s ∈ jec_leftRegion Vc) (hst : (offSupport Vc).Reachable s t)
    (hsoff : s ∉ Vc.support) :
    t ∈ jec_leftRegion Vc :=
  (inside_sameRegion_offSupport Vc hst hsoff).mp hs


theorem offSupport_component_monochromatic_out {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    {s t : Site 2} (hs : s ∉ jec_leftRegion Vc) (hst : (offSupport Vc).Reachable s t)
    (hsoff : s ∉ Vc.support) :
    t ∉ jec_leftRegion Vc :=
  fun ht => hs ((inside_sameRegion_offSupport Vc hst hsoff).mpr ht)


theorem hInOff_of_offSupport_connected {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    (hconn : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        (offSupport Vc).Reachable s t) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support := by
  intro s t hs ht
  exact offSupport_reachable_to_offSupportWalk Vc (hconn s t hs ht) (hoff s hs)


theorem inside_offSupport_connected_of_hub {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {c₀ : Site 2}
    (hhub : ∀ s : Site 2, s ∈ jec_leftRegion Vc → (offSupport Vc).Reachable c₀ s) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      (offSupport Vc).Reachable s t := by
  intro s t hs ht
  exact ((hhub s hs).symm).trans (hhub t ht)


theorem hInOff_of_interiorHub {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    {c₀ : Site 2}
    (hhub : ∀ s : Site 2, s ∈ jec_leftRegion Vc → (offSupport Vc).Reachable c₀ s) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support :=
  hInOff_of_offSupport_connected Vc hoff (inside_offSupport_connected_of_hub Vc hhub)


theorem hOutOff_of_exteriorHub {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hoff : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
    {d₀ : Site 2}
    (hhub : ∀ s : Site 2, s ∉ jec_leftRegion Vc → (offSupport Vc).Reachable d₀ s) :
    ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support := by
  intro s t hs ht
  have hconn : (offSupport Vc).Reachable s t := ((hhub s hs).symm).trans (hhub t ht)
  exact offSupport_reachable_to_offSupportWalk Vc hconn (hoff s hs)


theorem two_components_of_hubs {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    (hoffOut : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
    {c₀ d₀ : Site 2}
    (hubIn : ∀ s : Site 2, s ∈ jec_leftRegion Vc → (offSupport Vc).Reachable c₀ s)
    (hubOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → (offSupport Vc).Reachable d₀ s) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  jlri_two_components_of_offSupport_connected Vc hp hq
    (hInOff_of_interiorHub Vc hoffIn hubIn)
    (hOutOff_of_exteriorHub Vc hoffOut hubOut)


theorem minimalLoop_inside_sameRegion_offSupport (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {x y : Site 2}
    (h : (offSupport (mpl_orbitLoop K a)).Reachable x y) (hx : x ∉ (mpl_orbitLoop K a).support) :
    (x ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ y ∈ jec_leftRegion (mpl_orbitLoop K a)) :=
  inside_sameRegion_offSupport (mpl_orbitLoop K a) h hx


theorem minimalLoop_hInOff_of_interiorHub (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hoff : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
    {c₀ : Site 2}
    (hhub : ∀ s : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) →
        (offSupport (mpl_orbitLoop K a)).Reachable c₀ s) :
    ∀ s t : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) →
      t ∈ jec_leftRegion (mpl_orbitLoop K a) →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ (mpl_orbitLoop K a).support :=
  hInOff_of_interiorHub (mpl_orbitLoop K a) hoff hhub


theorem minimalLoop_two_components_of_hubs (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p (mpl_orbitLoop K a)))
    (hq : ∀ w ∈ (mpl_orbitLoop K a).support, w 0 ≤ q 0 - 1)
    (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
    (hoffOut : ∀ s ∉ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
    {c₀ d₀ : Site 2}
    (hubIn : ∀ s : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) →
        (offSupport (mpl_orbitLoop K a)).Reachable c₀ s)
    (hubOut : ∀ s : Site 2, s ∉ jec_leftRegion (mpl_orbitLoop K a) →
        (offSupport (mpl_orbitLoop K a)).Reachable d₀ s) :
    Nat.card (latticeMinusBarrier (jec_leftRegion (mpl_orbitLoop K a))).ConnectedComponent = 2 :=
  two_components_of_hubs (mpl_orbitLoop K a) hp hq hoffIn hoffOut hubIn hubOut


end Lattice
end StatMech
