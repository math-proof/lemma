/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part2


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

theorem ons_outsideConnector_ne_nil (dx dy top : ℤ) :
    ons_outsideConnector dx dy top ≠ [] := by
  simp [ons_outsideConnector]

@[simp] theorem ons_outsideConnector_head
    (dx dy top : ℤ) :
    (ons_outsideConnector dx dy top).head! = 0 := by
  simp [ons_outsideConnector]

@[simp] theorem ons_outsideConnector_getLast
    (dx dy top : ℤ) :
    (ons_outsideConnector dx dy top).getLast! = 0 := by
  simp [ons_outsideConnector, List.getLast!]

theorem ons_outsideConnector_displacement
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    ons_pathDisplacement (ons_outsideConnector dx dy top) = (-dx, -dy) := by
  have hu : 0 ≤ top - dy := by omega
  have hw : 0 ≤ dx + 2 := by omega
  have hv : 0 ≤ top := by omega
  simp only [ons_outsideConnector, ons_pathDisplacement_append,
    ons_pathDisplacement_replicate, ons_pathDisplacement_cons,
    ons_pathDisplacement_nil]
  simp [stepOf, Prod.smul_mk, nsmul_eq_mul,
    Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hw,
    Int.toNat_of_nonneg hv]
  constructor <;> ring

theorem ons_openTurnSum_five_blocks
    (a b c d e : Fin 4) (na nb nc nd ne : ℕ) :
    ons_openTurnSum
        (List.replicate (na + 1) a ++
          List.replicate (nb + 1) b ++
          List.replicate (nc + 1) c ++
          List.replicate (nd + 1) d ++
          List.replicate (ne + 1) e) =
      ons_turnPow a b + ons_turnPow b c +
        ons_turnPow c d + ons_turnPow d e := by
  let A := List.replicate (na + 1) a
  let B := List.replicate (nb + 1) b
  let C := List.replicate (nc + 1) c
  let D := List.replicate (nd + 1) d
  let E := List.replicate (ne + 1) e
  have hA : A ≠ [] := by simp [A]
  have hB : B ≠ [] := by simp [B]
  have hC : C ≠ [] := by simp [C]
  have hD : D ≠ [] := by simp [D]
  have hE : E ≠ [] := by simp [E]
  change ons_openTurnSum (A ++ B ++ C ++ D ++ E) = _
  simp only [List.append_assoc]
  rw [ons_openTurnSum_append A (B ++ (C ++ (D ++ E))) hA (by simp [hB]),
    ons_openTurnSum_append B (C ++ (D ++ E)) hB (by simp [hC]),
    ons_openTurnSum_append C (D ++ E) hC (by simp [hD]),
    ons_openTurnSum_append D E hD hE]
  simp [A, B, C, D, E, ons_openTurnSum_replicate]
  abel

theorem ons_outsideConnector_openTurnSum
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    ons_openTurnSum (ons_outsideConnector dx dy top) = 4 := by
  have hu : 0 < (top - dy).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hw : 0 < (dx + 2).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hv : 0 < top.toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  obtain ⟨u, hu'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hu)
  obtain ⟨w, hw'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
  obtain ⟨v, hv'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hv)
  rw [show ons_outsideConnector dx dy top =
      List.replicate (0 + 1) 0 ++
        List.replicate (u + 1) 1 ++
        List.replicate (w + 1) 2 ++
        List.replicate (v + 1) 3 ++
        List.replicate (0 + 1) 0 by
      simp [ons_outsideConnector, hu', hw', hv']]
  rw [ons_openTurnSum_five_blocks]
  decide

theorem ons_mem_outsideConnector_vertices_dropLast
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices
      (ons_outsideConnector dx dy top)).dropLast) :
    z = 0 ∨
      (∃ k : ℕ, k < (top - dy).toNat ∧ z = (1, (k : ℤ))) ∨
      (∃ k : ℕ, k < (dx + 2).toNat ∧
        z = (1 - (k : ℤ), top - dy)) ∨
      (∃ k : ℕ, k < top.toNat ∧
        z = (-dx - 1, top - dy - (k : ℤ))) ∨
      z = (-dx - 1, -dy) := by
  let B := List.replicate (top - dy).toNat (1 : Fin 4)
  let C := List.replicate (dx + 2).toNat (2 : Fin 4)
  let D := List.replicate top.toNat (3 : Fin 4)
  have hu : 0 ≤ top - dy := by omega
  have hw : 0 ≤ dx + 2 := by omega
  have hv : 0 ≤ top := by omega
  have hshape : ons_outsideConnector dx dy top =
      [0] ++ (B ++ (C ++ (D ++ [0]))) := by
    simp [ons_outsideConnector, B, C, D, List.append_assoc]
  rw [hshape] at hz
  rcases (ons_mem_pathVertices_append_dropLast_iff
      [0] (B ++ (C ++ (D ++ [0]))) z).mp hz with hstart | ⟨z₁, hz₁, ez₁⟩
  · left
    simpa [ons_pathVertices] using hstart
  rcases (ons_mem_pathVertices_append_dropLast_iff
      B (C ++ (D ++ [0])) z₁).mp hz₁ with hright | ⟨z₂, hz₂, ez₂⟩
  · right; left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        (top - dy).toNat 1 z₁).mp (by simpa [B] using hright)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, hkz]
    simp [ons_pathDisplacement, stepOf, Prod.smul_mk]
  rcases (ons_mem_pathVertices_append_dropLast_iff
      C (D ++ [0]) z₂).mp hz₂ with htopEdge | ⟨z₃, hz₃, ez₃⟩
  · right; right; left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        (dx + 2).toNat 2 z₂).mp (by simpa [C] using htopEdge)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, ez₂, hkz,
      show ons_pathDisplacement B =
          (top - dy).toNat • stepOf 1 by
        simp [B, ons_pathDisplacement_replicate]]
    simp [ons_pathDisplacement, stepOf, Prod.smul_mk,
      Int.toNat_of_nonneg hu]
    ring
  rcases (ons_mem_pathVertices_append_dropLast_iff
      D [0] z₃).mp hz₃ with hleft | ⟨z₄, hz₄, ez₄⟩
  · right; right; right; left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        top.toNat 3 z₃).mp (by simpa [D] using hleft)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, ez₂, ez₃, hkz,
      show ons_pathDisplacement B =
          (top - dy).toNat • stepOf 1 by
        simp [B, ons_pathDisplacement_replicate],
      show ons_pathDisplacement C =
          (dx + 2).toNat • stepOf 2 by
        simp [C, ons_pathDisplacement_replicate]]
    simp [ons_pathDisplacement, stepOf, Prod.smul_mk,
      Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hw]
    constructor <;> ring
  · right; right; right; right
    have hz₄zero : z₄ = 0 := by
      simpa [ons_pathVertices] using hz₄
    rw [ez₁, ez₂, ez₃, ez₄, hz₄zero,
      show ons_pathDisplacement B =
          (top - dy).toNat • stepOf 1 by
        simp [B, ons_pathDisplacement_replicate],
      show ons_pathDisplacement C =
          (dx + 2).toNat • stepOf 2 by
        simp [C, ons_pathDisplacement_replicate],
      show ons_pathDisplacement D = top.toNat • stepOf 3 by
        simp [D, ons_pathDisplacement_replicate]]
    simp [ons_pathDisplacement, stepOf, Prod.smul_mk,
      Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hw,
      Int.toNat_of_nonneg hv]
    constructor <;> ring

end StatMech.Onsager
