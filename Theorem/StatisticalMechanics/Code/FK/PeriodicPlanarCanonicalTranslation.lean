/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation.Part3
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]

@[simp] theorem PeriodicGraph.shiftBufferedEquiv_val
    (P : PeriodicGraph V) (z : Site 2) (n : Nat)
    (x : P.BufferedVertex n) :
    (P.shiftBufferedEquiv z n x : V) = P.shift z x.1 := rfl

theorem PeriodicGraph.shiftBufferedEquiv_adj
    (P : PeriodicGraph V) (z : Site 2) (n : Nat)
    (x y : P.BufferedVertex n) :
    (P.bufferedGraph n).Adj x y ↔
      (P.shiftedBufferedGraph z n).Adj
        (P.shiftBufferedEquiv z n x) (P.shiftBufferedEquiv z n y) := by
  exact (P.shift_adj z x.1 y.1).symm

theorem PeriodicGraph.shift_orbitBox_subset_orbitBox
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    P.shift z '' (P.orbitBox n : Set V) ⊆
      (P.orbitBox (n + flc_vrad z) : Set V) := by
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ P.orbitBox n at hx
  change P.shift z x ∈ P.orbitBox (n + flc_vrad z)
  rw [P.mem_orbitBox_iff] at hx ⊢
  obtain ⟨w, hw, u, hu, rfl⟩ := hx
  refine ⟨w + z, ?_, u, hu, ?_⟩
  · intro i
    calc
      ((w + z) i).natAbs ≤ (w i).natAbs + (z i).natAbs := by
        simpa only [Pi.add_apply] using Int.natAbs_add_le (w i) (z i)
      _ ≤ n + flc_vrad z :=
        Nat.add_le_add (hw i) (flc_vrad_le z i)
  · exact P.shift_add w z u

theorem PeriodicGraph.orbitBox_subset_shift_orbitBox
    (P : PeriodicGraph V) (z : Site 2) {a n : Nat}
    (h : a + flc_vrad z ≤ n) :
    (P.orbitBox a : Set V) ⊆ P.shift z '' (P.orbitBox n : Set V) := by
  intro x hx
  change x ∈ P.orbitBox a at hx
  rw [P.mem_orbitBox_iff] at hx
  obtain ⟨w, hw, u, hu, rfl⟩ := hx
  refine ⟨P.shift (w - z) u, ?_, ?_⟩
  · change P.shift (w - z) u ∈ P.orbitBox n
    rw [P.mem_orbitBox_iff]
    exact ⟨w - z, flc_box_subset_transBox z h hw, u, hu, rfl⟩
  · rw [← P.shift_add (w - z) z u]
    congr 2
    ext i
    simp

theorem PeriodicGraph.bufferedRadius_add_le
    (P : PeriodicGraph V) (n c : Nat) :
    P.bufferedRadius n + c ≤ P.bufferedRadius (n + c) := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Nat.add_succ, Nat.add_succ]
      exact (Nat.succ_le_succ ih).trans
        (Nat.succ_le_of_lt
          (P.bufferedRadius_strictMono (Nat.lt_succ_self (n + c))))

theorem PeriodicGraph.shiftedBuffered_subset_buffered
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    (P.shiftedBufferedVertices z n : Set V) ⊆
      (P.orbitBox (P.bufferedRadius (n + flc_vrad z)) : Set V) := by
  intro x hx
  rw [PeriodicGraph.shiftedBufferedVertices, Finset.coe_image] at hx
  exact P.orbitBox_mono
    (P.bufferedRadius_add_le n (flc_vrad z))
    (P.shift_orbitBox_subset_orbitBox z (P.bufferedRadius n) hx)

theorem PeriodicGraph.buffered_subset_shiftedBuffered
    (P : PeriodicGraph V) (z : Site 2) {a n : Nat}
    (h : a + flc_vrad z ≤ n) :
    (P.orbitBox (P.bufferedRadius a) : Set V) ⊆
      (P.shiftedBufferedVertices z n : Set V) := by
  intro x hx
  rw [PeriodicGraph.shiftedBufferedVertices, Finset.coe_image]
  apply P.orbitBox_subset_shift_orbitBox z
    (n := P.bufferedRadius n) _ hx
  exact (P.bufferedRadius_add_le a (flc_vrad z)).trans
    ((P.bufferedRadius_strictMono.le_iff_le).2 h)

end StatMech.FK.PeriodicPlanar
