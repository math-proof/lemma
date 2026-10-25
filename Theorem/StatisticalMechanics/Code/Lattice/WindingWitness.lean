/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
open SimpleGraph Function Set Finset


namespace StatMech

namespace Lattice

theorem wwit_singleVisit_localTurn_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (f : Site 2) (i : ℕ)
    (h : usc_visitSet K a f = {i}) :
    usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 := by
  rw [usc_singleVisit_local_turn K a f i h]
  exact turnZ_mem K _


theorem wwit_localTurn_mem (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) (f : Site 2) :
    usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 := by
  classical
  rcases Nat.eq_zero_or_pos (usc_visitSet K a f).card with h0 | hpos
  · 
    right; left
    unfold usc_localTurn
    rw [Finset.card_eq_zero] at h0
    rw [h0, Finset.sum_empty]
  · 
    have hcard1 : (usc_visitSet K a f).card = 1 := hmult f hpos
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard1
    exact wwit_singleVisit_localTurn_mem K a f i hi


theorem wwit_localTurn_mem_orbitFaces (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hmult : usc_FaceMultiplicityOne K a)
    (f : Site 2) (_hf : f ∈ usc_orbitFaces K a) :
    usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 :=
  wwit_localTurn_mem K a hmult f


theorem wwit_localTurn_sum_eq_totalTurn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    ∑ f ∈ usc_orbitFaces K a, usc_localTurn K a f
      = totalTurnZ K a.1 (dartOrbitPeriod K a) :=
  (usc_totalTurnZ_eq_sum_localTurn K a).symm


theorem wwit_exists_pos_of_sum_eq_four {s : Finset (Site 2)} (g : Site 2 → ℤ)
    (hg : ∀ f ∈ s, g f = 1 ∨ g f = 0 ∨ g f = -1)
    (hsum : ∑ f ∈ s, g f = 4) :
    ∃ f ∈ s, g f = 1 := by
  by_contra hcon
  push Not at hcon
  
  have hle : ∀ f ∈ s, g f ≤ 0 := by
    intro f hf
    rcases hg f hf with h | h | h
    · exact absurd h (hcon f hf)
    · omega
    · omega
  have : (∑ f ∈ s, g f) ≤ 0 := Finset.sum_nonpos hle
  omega


theorem wwit_exists_neg_of_sum_eq_negFour {s : Finset (Site 2)} (g : Site 2 → ℤ)
    (hg : ∀ f ∈ s, g f = 1 ∨ g f = 0 ∨ g f = -1)
    (hsum : ∑ f ∈ s, g f = -4) :
    ∃ f ∈ s, g f = -1 := by
  by_contra hcon
  push Not at hcon
  have hge : ∀ f ∈ s, 0 ≤ g f := by
    intro f hf
    rcases hg f hf with h | h | h
    · omega
    · omega
    · exact absurd h (hcon f hf)
  have : (0 : ℤ) ≤ ∑ f ∈ s, g f := Finset.sum_nonneg hge
  omega


theorem wwit_exists_convex_corner (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) (hturn : TurningIsFullRevolution K a) :
    (∃ f ∈ usc_orbitFaces K a, usc_localTurn K a f = 1) ∨
      (∃ f ∈ usc_orbitFaces K a, usc_localTurn K a f = -1) := by
  have hsum := wwit_localTurn_sum_eq_totalTurn K a
  rcases hturn with h4 | hm4
  · left
    rw [h4] at hsum
    exact wwit_exists_pos_of_sum_eq_four (usc_localTurn K a)
      (fun f hf => wwit_localTurn_mem_orbitFaces K a hmult f hf) hsum
  · right
    rw [hm4] at hsum
    exact wwit_exists_neg_of_sum_eq_negFour (usc_localTurn K a)
      (fun f hf => wwit_localTurn_mem_orbitFaces K a hmult f hf) hsum


theorem wwit_starHull_localTurn_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) (f : Site 2) :
    usc_localTurn (ndt_StarHull K) a f = 1 ∨ usc_localTurn (ndt_StarHull K) a f = 0 ∨
      usc_localTurn (ndt_StarHull K) a f = -1 :=
  wwit_localTurn_mem (ndt_StarHull K) a (ndt_faceMultiplicityOne K a) f


theorem wwit_starHull_exists_convex_corner (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hturn : TurningIsFullRevolution (ndt_StarHull K) a) :
    (∃ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f = 1) ∨
      (∃ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f = -1) :=
  wwit_exists_convex_corner (ndt_StarHull K) a (ndt_faceMultiplicityOne K a) hturn


theorem wwit_dart_of_localTurn_one (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) (f : Site 2) (hf1 : usc_localTurn K a f = 1) :
    ∃ i : ℕ, i ∈ usc_visitSet K a f ∧
      dartFace ((dartNext K)^[i] a.1) = f ∧ turnZ K ((dartNext K)^[i] a.1) = 1 := by
  classical
  
  have hpos : 1 ≤ (usc_visitSet K a f).card := by
    by_contra hcon
    push Not at hcon
    have h0 : (usc_visitSet K a f).card = 0 := by omega
    rw [Finset.card_eq_zero] at h0
    rw [usc_localTurn, h0, Finset.sum_empty] at hf1
    exact absurd hf1 (by norm_num)
  
  have hcard1 : (usc_visitSet K a f).card = 1 := hmult f hpos
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard1
  have himem : i ∈ usc_visitSet K a f := by rw [hi]; exact Finset.mem_singleton_self i
  have hface : dartFace ((dartNext K)^[i] a.1) = f := by
    simp only [usc_visitSet, Finset.mem_filter, Finset.mem_range] at himem
    exact himem.2
  have hturn : turnZ K ((dartNext K)^[i] a.1) = 1 := by
    have := usc_singleVisit_local_turn K a f i hi
    rw [hf1] at this
    exact this.symm
  exact ⟨i, himem, hface, hturn⟩


theorem wwit_cornerCell_mem (K : Set (Site 2)) (e : Dart) (hturn : turnZ K e = 1) :
    e.head + (-rot90Fun e.dir) ∈ K := by
  classical
  unfold turnZ at hturn
  by_contra hmem
  rw [if_neg hmem] at hturn
  split_ifs at hturn with hb
  all_goals simp_all


end Lattice
end StatMech
