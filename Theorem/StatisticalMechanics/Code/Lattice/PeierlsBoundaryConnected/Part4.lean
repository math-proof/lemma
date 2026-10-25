/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ClusterBoundaryRecovery.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsEulerParity
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Def.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem mem_boxFrame_bottom (m n : ℕ) (a : ℤ) (h1 : -1 ≤ a) (h2 : a ≤ m) :
    (![a, -1] : Site 2) ∈ boxFrame m n := by
  unfold boxFrame
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_union]
  left; left; left
  rw [Finset.mem_image]; exact ⟨a, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩

theorem mem_boxFrame_top (m n : ℕ) (a : ℤ) (h1 : -1 ≤ a) (h2 : a ≤ m) :
    (![a, (n:ℤ)] : Site 2) ∈ boxFrame m n := by
  unfold boxFrame
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_union]
  left; left; right
  rw [Finset.mem_image]; exact ⟨a, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩

theorem mem_boxFrame_left (m n : ℕ) (b : ℤ) (h1 : -1 ≤ b) (h2 : b ≤ n) :
    (![(-1:ℤ), b] : Site 2) ∈ boxFrame m n := by
  unfold boxFrame
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_union]
  left; right
  rw [Finset.mem_image]; exact ⟨b, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩

theorem mem_boxFrame_right (m n : ℕ) (b : ℤ) (h1 : -1 ≤ b) (h2 : b ≤ n) :
    (![(m:ℤ), b] : Site 2) ∈ boxFrame m n := by
  unfold boxFrame
  rw [Finset.mem_union]
  right
  rw [Finset.mem_image]; exact ⟨b, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩


theorem boxFrame_bottom_adj (m n : ℕ) (a : ℤ) (h1 : 0 ≤ a + 1) (h2 : a + 1 ≤ m) :
    (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj ![a, -1] ![a + 1, -1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨latAdj_right a (-1), ?_⟩
  rw [sharedPrimalEdge_right]; unfold faceCorner10 faceCorner11
  rw [bdEdge_mk, mem_box_coords, mem_box_coords, show ((-1:ℤ) + 1) = 0 from by ring]
  exact ⟨fun ⟨_, _, h3, _⟩ => by omega, fun h => absurd ⟨h1, h2, le_refl 0, Nat.cast_nonneg n⟩ h⟩


theorem boxFrame_top_adj (m n : ℕ) (a : ℤ) (h1 : 0 ≤ a + 1) (h2 : a + 1 ≤ m) :
    (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj ![a, (n:ℤ)] ![a + 1, (n:ℤ)] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨latAdj_right a (n:ℤ), ?_⟩
  rw [sharedPrimalEdge_right]; unfold faceCorner10 faceCorner11
  rw [bdEdge_mk, mem_box_coords, mem_box_coords]
  exact ⟨fun ⟨_, _, _, _⟩ ⟨_, _, _, hq⟩ => by omega,
    fun h => ⟨h1, h2, Nat.cast_nonneg n, le_refl _⟩⟩


theorem boxFrame_right_adj (m n : ℕ) (b : ℤ) (h1 : 0 ≤ b + 1) (h2 : b + 1 ≤ n) :
    (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj ![(m:ℤ), b] ![(m:ℤ), b + 1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨latAdj_top (m:ℤ) b, ?_⟩
  rw [sharedPrimalEdge_top]; unfold faceCorner01 faceCorner11
  rw [bdEdge_mk, mem_box_coords, mem_box_coords]
  exact ⟨fun _ ⟨hp1, hp2, _, _⟩ => by omega,
    fun h => ⟨Nat.cast_nonneg m, le_refl _, h1, h2⟩⟩


theorem boxFrame_left_adj (m n : ℕ) (b : ℤ) (h1 : 0 ≤ b + 1) (h2 : b + 1 ≤ n) :
    (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj ![(-1:ℤ), b] ![(-1:ℤ), b + 1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨latAdj_top (-1:ℤ) b, ?_⟩
  rw [sharedPrimalEdge_top]; unfold faceCorner01 faceCorner11
  rw [bdEdge_mk, mem_box_coords, mem_box_coords, show ((-1:ℤ) + 1) = 0 from by ring]
  exact ⟨fun ⟨hp, _, _, _⟩ => by omega,
    fun h => absurd ⟨le_refl 0, Nat.cast_nonneg m, h1, h2⟩ h⟩


theorem boxFrame_bottom_walk (m n : ℕ) (k : ℕ) (hk : k ≤ m + 1) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        ![(-1:ℤ), -1] ![(k:ℤ) - 1, -1], ∀ w ∈ p.support, w ∈ boxFrame m n := by
  induction k with
  | zero =>
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    have hw := SimpleGraph.Walk.mem_support_nil_iff.mp hw
    rw [hw]
    exact mem_boxFrame_bottom m n (-1) (le_refl _) (by omega)
  | succ j ih =>
    have hj : j ≤ m := by omega
    obtain ⟨p, hp⟩ := ih (by omega)
    have hjm : (j:ℤ) ≤ (m:ℤ) := by exact_mod_cast hj
    have hadj : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj
        ![(j:ℤ) - 1, -1] ![(j:ℤ), -1] := by
      have h := boxFrame_bottom_adj m n ((j:ℤ) - 1) (by omega) (by omega)
      rwa [show ((j:ℤ) - 1 + 1) = (j:ℤ) from by ring] at h
    refine ⟨(p.concat hadj).copy rfl (by rw [show (((j + 1 : ℕ):ℤ) - 1) = (j:ℤ) from by
      push_cast; ring]), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_concat, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hp w hw
    · rw [List.mem_singleton] at hw; rw [hw]
      exact mem_boxFrame_bottom m n (j:ℤ) (by omega) hjm


theorem boxFrame_left_walk (m n : ℕ) (k : ℕ) (hk : k ≤ n + 1) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        ![(-1:ℤ), -1] ![(-1:ℤ), (k:ℤ) - 1], ∀ w ∈ p.support, w ∈ boxFrame m n := by
  induction k with
  | zero =>
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    have hw := SimpleGraph.Walk.mem_support_nil_iff.mp hw
    rw [hw]
    exact mem_boxFrame_left m n (-1) (le_refl _) (by omega)
  | succ j ih =>
    have hj : j ≤ n := by omega
    obtain ⟨p, hp⟩ := ih (by omega)
    have hjn : (j:ℤ) ≤ (n:ℤ) := by exact_mod_cast hj
    have hadj : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj
        ![(-1:ℤ), (j:ℤ) - 1] ![(-1:ℤ), (j:ℤ)] := by
      have h := boxFrame_left_adj m n ((j:ℤ) - 1) (by omega) (by omega)
      rwa [show ((j:ℤ) - 1 + 1) = (j:ℤ) from by ring] at h
    refine ⟨(p.concat hadj).copy rfl (by rw [show (((j + 1 : ℕ):ℤ) - 1) = (j:ℤ) from by
      push_cast; ring]), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_concat, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hp w hw
    · rw [List.mem_singleton] at hw; rw [hw]
      exact mem_boxFrame_left m n (j:ℤ) (by omega) hjn


theorem boxFrame_right_walk (m n : ℕ) (k : ℕ) (hk : k ≤ n + 1) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        ![(m:ℤ), -1] ![(m:ℤ), (k:ℤ) - 1], ∀ w ∈ p.support, w ∈ boxFrame m n := by
  induction k with
  | zero =>
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    have hw := SimpleGraph.Walk.mem_support_nil_iff.mp hw
    rw [hw]
    exact mem_boxFrame_right m n (-1) (le_refl _) (by omega)
  | succ j ih =>
    have hj : j ≤ n := by omega
    obtain ⟨p, hp⟩ := ih (by omega)
    have hjn : (j:ℤ) ≤ (n:ℤ) := by exact_mod_cast hj
    have hadj : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj
        ![(m:ℤ), (j:ℤ) - 1] ![(m:ℤ), (j:ℤ)] := by
      have h := boxFrame_right_adj m n ((j:ℤ) - 1) (by omega) (by omega)
      rwa [show ((j:ℤ) - 1 + 1) = (j:ℤ) from by ring] at h
    refine ⟨(p.concat hadj).copy rfl (by rw [show (((j + 1 : ℕ):ℤ) - 1) = (j:ℤ) from by
      push_cast; ring]), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_concat, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hp w hw
    · rw [List.mem_singleton] at hw; rw [hw]
      exact mem_boxFrame_right m n (j:ℤ) (by omega) hjn


theorem boxFrame_top_walk (m n : ℕ) (k : ℕ) (hk : k ≤ m + 1) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        ![(-1:ℤ), (n:ℤ)] ![(k:ℤ) - 1, (n:ℤ)], ∀ w ∈ p.support, w ∈ boxFrame m n := by
  induction k with
  | zero =>
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    have hw := SimpleGraph.Walk.mem_support_nil_iff.mp hw
    rw [hw]
    exact mem_boxFrame_top m n (-1) (le_refl _) (by omega)
  | succ j ih =>
    have hj : j ≤ m := by omega
    obtain ⟨p, hp⟩ := ih (by omega)
    have hjm : (j:ℤ) ≤ (m:ℤ) := by exact_mod_cast hj
    have hadj : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj
        ![(j:ℤ) - 1, (n:ℤ)] ![(j:ℤ), (n:ℤ)] := by
      have h := boxFrame_top_adj m n ((j:ℤ) - 1) (by omega) (by omega)
      rwa [show ((j:ℤ) - 1 + 1) = (j:ℤ) from by ring] at h
    refine ⟨(p.concat hadj).copy rfl (by rw [show (((j + 1 : ℕ):ℤ) - 1) = (j:ℤ) from by
      push_cast; ring]), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_concat, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hp w hw
    · rw [List.mem_singleton] at hw; rw [hw]
      exact mem_boxFrame_top m n (j:ℤ) (by omega) hjm


theorem mem_boxFrame_cases (m n : ℕ) (v : Site 2) (hv : v ∈ boxFrame m n) :
    (∃ a : ℤ, -1 ≤ a ∧ a ≤ m ∧ v = ![a, -1]) ∨
    (∃ a : ℤ, -1 ≤ a ∧ a ≤ m ∧ v = ![a, (n:ℤ)]) ∨
    (∃ b : ℤ, -1 ≤ b ∧ b ≤ n ∧ v = ![(-1:ℤ), b]) ∨
    (∃ b : ℤ, -1 ≤ b ∧ b ≤ n ∧ v = ![(m:ℤ), b]) := by
  unfold boxFrame at hv
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_union] at hv
  rcases hv with ((hb | ht) | hl) | hr
  · rw [Finset.mem_image] at hb; obtain ⟨a, ha, rfl⟩ := hb
    rw [Finset.mem_Icc] at ha; exact Or.inl ⟨a, ha.1, ha.2, rfl⟩
  · rw [Finset.mem_image] at ht; obtain ⟨a, ha, rfl⟩ := ht
    rw [Finset.mem_Icc] at ha; exact Or.inr (Or.inl ⟨a, ha.1, ha.2, rfl⟩)
  · rw [Finset.mem_image] at hl; obtain ⟨b, hb, rfl⟩ := hl
    rw [Finset.mem_Icc] at hb; exact Or.inr (Or.inr (Or.inl ⟨b, hb.1, hb.2, rfl⟩))
  · rw [Finset.mem_image] at hr; obtain ⟨b, hb, rfl⟩ := hr
    rw [Finset.mem_Icc] at hb; exact Or.inr (Or.inr (Or.inr ⟨b, hb.1, hb.2, rfl⟩))


theorem mem_boxFrame_corner (m n : ℕ) : (![(-1:ℤ), -1] : Site 2) ∈ boxFrame m n :=
  mem_boxFrame_bottom m n (-1) (le_refl _) (by omega)


theorem boxFrame_bottom_to_corner (m n : ℕ) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        ![(-1:ℤ), -1] ![(m:ℤ), -1], ∀ w ∈ p.support, w ∈ boxFrame m n := by
  obtain ⟨p, hp⟩ := boxFrame_bottom_walk m n (m + 1) (le_refl _)
  refine ⟨p.copy rfl ((site2_eq _ _ _ _).mpr ⟨by push_cast; ring, rfl⟩), ?_⟩
  intro w hw; rw [SimpleGraph.Walk.support_copy] at hw; exact hp w hw


theorem boxFrame_left_to_corner (m n : ℕ) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        ![(-1:ℤ), -1] ![(-1:ℤ), (n:ℤ)], ∀ w ∈ p.support, w ∈ boxFrame m n := by
  obtain ⟨p, hp⟩ := boxFrame_left_walk m n (n + 1) (le_refl _)
  refine ⟨p.copy rfl ((site2_eq _ _ _ _).mpr ⟨rfl, by push_cast; ring⟩), ?_⟩
  intro w hw; rw [SimpleGraph.Walk.support_copy] at hw; exact hp w hw


theorem boxFrame_walk_from_corner (m n : ℕ) {v : Site 2} (hv : v ∈ boxFrame m n) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk ![(-1:ℤ), -1] v,
      ∀ w ∈ p.support, w ∈ boxFrame m n := by
  rcases mem_boxFrame_cases m n v hv with ⟨a, ha1, ha2, rfl⟩ | ⟨a, ha1, ha2, rfl⟩ |
    ⟨b, hb1, hb2, rfl⟩ | ⟨b, hb1, hb2, rfl⟩
  · 
    obtain ⟨p, hp⟩ := boxFrame_bottom_walk m n (a + 1).toNat (by omega)
    refine ⟨p.copy rfl ((site2_eq _ _ _ _).mpr ⟨by omega, rfl⟩), ?_⟩
    intro w hw; rw [SimpleGraph.Walk.support_copy] at hw; exact hp w hw
  · 
    obtain ⟨p1, hp1⟩ := boxFrame_left_to_corner m n
    obtain ⟨p2, hp2⟩ := boxFrame_top_walk m n (a + 1).toNat (by omega)
    refine ⟨p1.append (p2.copy rfl ((site2_eq _ _ _ _).mpr ⟨by omega, rfl⟩)), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hp1 w hw
    · have hw := List.mem_of_mem_tail hw
      rw [SimpleGraph.Walk.support_copy] at hw; exact hp2 w hw
  · 
    obtain ⟨p, hp⟩ := boxFrame_left_walk m n (b + 1).toNat (by omega)
    refine ⟨p.copy rfl ((site2_eq _ _ _ _).mpr ⟨rfl, by omega⟩), ?_⟩
    intro w hw; rw [SimpleGraph.Walk.support_copy] at hw; exact hp w hw
  · 
    obtain ⟨p1, hp1⟩ := boxFrame_bottom_to_corner m n
    obtain ⟨p2, hp2⟩ := boxFrame_right_walk m n (b + 1).toNat (by omega)
    refine ⟨p1.append (p2.copy rfl ((site2_eq _ _ _ _).mpr ⟨rfl, by omega⟩)), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hp1 w hw
    · have hw := List.mem_of_mem_tail hw
      rw [SimpleGraph.Walk.support_copy] at hw; exact hp2 w hw


theorem boxCluster_faceBoundaryConnected (m n : ℕ) :
    FaceBoundaryConnected (↑(boxCluster m n) : Set (Site 2)) (boxFrame m n) := by
  apply faceBoundaryConnected_of_walks ⟨_, mem_boxFrame_corner m n⟩
  intro f hf g hg
  obtain ⟨pf, hpf⟩ := boxFrame_walk_from_corner m n hf
  obtain ⟨pg, hpg⟩ := boxFrame_walk_from_corner m n hg
  refine ⟨pf.reverse.append pg, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_append] at hw
  rcases List.mem_append.mp hw with hwf | hwg
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hwf
    exact hpf w hwf
  · exact hpg w (List.mem_of_mem_tail hwg)


theorem straddle_implies_frame (m n : ℕ) (a b : ℤ)
    (hin : (0 ≤ a ∧ a ≤ m ∧ 0 ≤ b ∧ b ≤ n) ∨ (0 ≤ a + 1 ∧ a + 1 ≤ m ∧ 0 ≤ b ∧ b ≤ n) ∨
      (0 ≤ a + 1 ∧ a + 1 ≤ m ∧ 0 ≤ b + 1 ∧ b + 1 ≤ n) ∨ (0 ≤ a ∧ a ≤ m ∧ 0 ≤ b + 1 ∧ b + 1 ≤ n))
    (hout : ¬(0 ≤ a ∧ a ≤ m ∧ 0 ≤ b ∧ b ≤ n) ∨ ¬(0 ≤ a + 1 ∧ a + 1 ≤ m ∧ 0 ≤ b ∧ b ≤ n) ∨
      ¬(0 ≤ a + 1 ∧ a + 1 ≤ m ∧ 0 ≤ b + 1 ∧ b + 1 ≤ n) ∨
      ¬(0 ≤ a ∧ a ≤ m ∧ 0 ≤ b + 1 ∧ b + 1 ≤ n)) :
    (-1 ≤ a ∧ a ≤ m ∧ b = -1) ∨ (-1 ≤ a ∧ a ≤ m ∧ b = (n:ℤ)) ∨
    (a = -1 ∧ -1 ≤ b ∧ b ≤ n) ∨ (a = (m:ℤ) ∧ -1 ≤ b ∧ b ≤ n) := by
  omega


theorem bdInd_eq_zero_of_sameSide (m n : ℕ) (x y : Site 2)
    (h : (x ∈ (↑(boxCluster m n) : Set (Site 2))) ↔ (y ∈ (↑(boxCluster m n) : Set (Site 2)))) :
    bdInd (↑(boxCluster m n) : Set (Site 2)) x y = 0 := by
  unfold bdInd
  rw [if_neg]
  by_cases hx : x ∈ (↑(boxCluster m n) : Set (Site 2)) <;>
    by_cases hy : y ∈ (↑(boxCluster m n) : Set (Site 2)) <;> simp_all


theorem support_boxCluster_subset_frame (m n : ℕ) :
    (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).support
      ⊆ (boxFrame m n : Set (Site 2)) := by
  intro f hf
  rw [SimpleGraph.mem_support] at hf
  obtain ⟨g, hadj⟩ := hf
  have hfeq : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  have hdeg : 0 < faceBoundaryDegree (↑(boxCluster m n) : Set (Site 2)) (f 0) (f 1) := by
    rw [← degree_faceBoundaryGraph, ← hfeq]; exact hadj.degree_pos_left
  
  have c00 : (faceCorner00 (f 0) (f 1)) ∈ (↑(boxCluster m n) : Set (Site 2)) ↔
      (0 ≤ f 0 ∧ f 0 ≤ m ∧ 0 ≤ f 1 ∧ f 1 ≤ n) := by unfold faceCorner00; rw [mem_box_coords]
  have c10 : (faceCorner10 (f 0) (f 1)) ∈ (↑(boxCluster m n) : Set (Site 2)) ↔
      (0 ≤ f 0 + 1 ∧ f 0 + 1 ≤ m ∧ 0 ≤ f 1 ∧ f 1 ≤ n) := by unfold faceCorner10; rw [mem_box_coords]
  have c11 : (faceCorner11 (f 0) (f 1)) ∈ (↑(boxCluster m n) : Set (Site 2)) ↔
      (0 ≤ f 0 + 1 ∧ f 0 + 1 ≤ m ∧ 0 ≤ f 1 + 1 ∧ f 1 + 1 ≤ n) := by
    unfold faceCorner11; rw [mem_box_coords]
  have c01 : (faceCorner01 (f 0) (f 1)) ∈ (↑(boxCluster m n) : Set (Site 2)) ↔
      (0 ≤ f 0 ∧ f 0 ≤ m ∧ 0 ≤ f 1 + 1 ∧ f 1 + 1 ≤ n) := by unfold faceCorner01; rw [mem_box_coords]
  
  have hbothdir : (∃ c : Site 2, c ∈ ({faceCorner00 (f 0) (f 1), faceCorner10 (f 0) (f 1),
        faceCorner11 (f 0) (f 1), faceCorner01 (f 0) (f 1)} : Set (Site 2)) ∧
        c ∈ (↑(boxCluster m n) : Set (Site 2))) ∧
      (∃ c : Site 2, c ∈ ({faceCorner00 (f 0) (f 1), faceCorner10 (f 0) (f 1),
        faceCorner11 (f 0) (f 1), faceCorner01 (f 0) (f 1)} : Set (Site 2)) ∧
        c ∉ (↑(boxCluster m n) : Set (Site 2))) := by
    by_contra hcon
    rw [not_and_or] at hcon
    have hbd0 : faceBoundaryDegree (↑(boxCluster m n) : Set (Site 2)) (f 0) (f 1) = 0 := by
      unfold faceBoundaryDegree
      have key : ∀ x ∈ ({faceCorner00 (f 0) (f 1), faceCorner10 (f 0) (f 1),
          faceCorner11 (f 0) (f 1), faceCorner01 (f 0) (f 1)} : Set (Site 2)),
          ∀ y ∈ ({faceCorner00 (f 0) (f 1), faceCorner10 (f 0) (f 1),
          faceCorner11 (f 0) (f 1), faceCorner01 (f 0) (f 1)} : Set (Site 2)),
          (x ∈ (↑(boxCluster m n) : Set (Site 2))) ↔ (y ∈ (↑(boxCluster m n) : Set (Site 2))) := by
        rcases hcon with hcon | hcon
        · 
          push Not at hcon
          intro x hx y hy
          exact iff_of_false (hcon x hx) (hcon y hy)
        · 
          push Not at hcon
          intro x hx y hy
          exact iff_of_true (hcon x hx) (hcon y hy)
      set z00 := faceCorner00 (f 0) (f 1)
      set z10 := faceCorner10 (f 0) (f 1)
      set z11 := faceCorner11 (f 0) (f 1)
      set z01 := faceCorner01 (f 0) (f 1)
      have h00 := bdInd_eq_zero_of_sameSide m n z00 z10
        (key _ (by left; rfl) _ (by right; left; rfl))
      have h10 := bdInd_eq_zero_of_sameSide m n z10 z11
        (key _ (by right; left; rfl) _ (by right; right; left; rfl))
      have h11 := bdInd_eq_zero_of_sameSide m n z11 z01
        (key _ (by right; right; left; rfl) _ (by right; right; right; rfl))
      have h01 := bdInd_eq_zero_of_sameSide m n z01 z00
        (key _ (by right; right; right; rfl) _ (by left; rfl))
      rw [h00, h10, h11, h01]
    omega
  
  obtain ⟨⟨ci, hci, hciin⟩, ⟨co, hco, hcoout⟩⟩ := hbothdir
  rw [hfeq, Finset.mem_coe]
  
  have hin : (0 ≤ f 0 ∧ f 0 ≤ m ∧ 0 ≤ f 1 ∧ f 1 ≤ n) ∨
      (0 ≤ f 0 + 1 ∧ f 0 + 1 ≤ m ∧ 0 ≤ f 1 ∧ f 1 ≤ n) ∨
      (0 ≤ f 0 + 1 ∧ f 0 + 1 ≤ m ∧ 0 ≤ f 1 + 1 ∧ f 1 + 1 ≤ n) ∨
      (0 ≤ f 0 ∧ f 0 ≤ m ∧ 0 ≤ f 1 + 1 ∧ f 1 + 1 ≤ n) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hci
    rcases hci with rfl | rfl | rfl | rfl
    · exact Or.inl (c00.mp hciin)
    · exact Or.inr (Or.inl (c10.mp hciin))
    · exact Or.inr (Or.inr (Or.inl (c11.mp hciin)))
    · exact Or.inr (Or.inr (Or.inr (c01.mp hciin)))
  have hout : ¬(0 ≤ f 0 ∧ f 0 ≤ m ∧ 0 ≤ f 1 ∧ f 1 ≤ n) ∨
      ¬(0 ≤ f 0 + 1 ∧ f 0 + 1 ≤ m ∧ 0 ≤ f 1 ∧ f 1 ≤ n) ∨
      ¬(0 ≤ f 0 + 1 ∧ f 0 + 1 ≤ m ∧ 0 ≤ f 1 + 1 ∧ f 1 + 1 ≤ n) ∨
      ¬(0 ≤ f 0 ∧ f 0 ≤ m ∧ 0 ≤ f 1 + 1 ∧ f 1 + 1 ≤ n) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hco
    rcases hco with rfl | rfl | rfl | rfl
    · exact Or.inl (fun h => hcoout (c00.mpr h))
    · exact Or.inr (Or.inl (fun h => hcoout (c10.mpr h)))
    · exact Or.inr (Or.inr (Or.inl (fun h => hcoout (c11.mpr h))))
    · exact Or.inr (Or.inr (Or.inr (fun h => hcoout (c01.mpr h))))
  rcases straddle_implies_frame m n (f 0) (f 1) hin hout with
    ⟨h1, h2, hb⟩ | ⟨h1, h2, hb⟩ | ⟨ha, h2, h3⟩ | ⟨ha, h2, h3⟩
  · rw [hb]; exact mem_boxFrame_bottom m n (f 0) h1 h2
  · rw [hb]; exact mem_boxFrame_top m n (f 0) h1 h2
  · rw [ha]; exact mem_boxFrame_left m n (f 1) h2 h3
  · rw [ha]; exact mem_boxFrame_right m n (f 1) h2 h3


theorem boxCluster_single_dualCircuit (m n : ℕ) :
    ∃ c : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk ![(-1:ℤ), -1] ![(-1:ℤ), -1],
      c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).edgeSet,
        e ∈ c.edges :=
  faceBoundaryGraph_single_dualCircuit (support_boxCluster_subset_frame m n)
    (boxCluster_faceBoundaryConnected m n) (mem_boxFrame_corner m n)

end Lattice
end StatMech
