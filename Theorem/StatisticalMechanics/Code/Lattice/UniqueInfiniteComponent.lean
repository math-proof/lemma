/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Def.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent
open Set SimpleGraph


namespace StatMech

namespace Lattice

variable {d : ℕ}


@[simp]
theorem mem_exterior {d R : ℕ} {x : Site d} :
    x ∈ exterior d R ↔ ∃ i, R < (x i).natAbs := Iff.rfl


theorem exterior_eq_compl_box (d R : ℕ) : exterior d R = (box d R)ᶜ := by
  ext x
  simp only [mem_exterior, mem_box, Set.mem_compl_iff, not_forall, not_le]


theorem segment_up (S : Set (Site d)) (j : Fin d) (p : Site d) (c : ℤ) (hpc : p j ≤ c)
    (hp : p ∈ S) (hc : Function.update p j c ∈ S)
    (hseg : ∀ z : ℤ, (p j ≤ z ∧ z ≤ c) → Function.update p j z ∈ S) :
    ((hypercubicLattice d).induce S).Reachable ⟨p, hp⟩ ⟨Function.update p j c, hc⟩ := by
  set n := (c - p j).toNat with hn
  have hntoNat : (n : ℤ) = c - p j := by rw [hn]; exact Int.toNat_of_nonneg (by linarith)
  have hmem : ∀ t ≤ n, Function.update p j (p j + (t : ℤ)) ∈ S := by
    intro t ht
    apply hseg
    refine ⟨by linarith, ?_⟩
    have : (t : ℤ) ≤ (n : ℤ) := by exact_mod_cast ht
    linarith [hntoNat]
  have key := segment_connectedWithin S j p n hmem
  have hstart : Function.update p j (p j + (0 : ℤ)) = p := by
    rw [add_zero, Function.update_eq_self]
  have hend : Function.update p j (p j + (n : ℤ)) = Function.update p j c := by
    rw [hntoNat]; ring_nf
  convert key using 2
  · rw [hstart]
  · rw [hend]


theorem segment_gen (S : Set (Site d)) (j : Fin d) (p : Site d) (c : ℤ)
    (hp : p ∈ S) (hc : Function.update p j c ∈ S)
    (hseg : ∀ z : ℤ, (min (p j) c ≤ z ∧ z ≤ max (p j) c) → Function.update p j z ∈ S) :
    ((hypercubicLattice d).induce S).Reachable ⟨p, hp⟩ ⟨Function.update p j c, hc⟩ := by
  rcases le_total (p j) c with h | h
  · apply segment_up S j p c h hp hc
    intro z hz
    apply hseg
    rw [min_eq_left h, max_eq_right h]; exact hz
  · set q := Function.update p j c with hq
    have hqj : q j = c := Function.update_self j c p
    have hupd : Function.update q j (p j) = p := by
      rw [hq, Function.update_idem, Function.update_eq_self]
    have hcp : Function.update q j (p j) ∈ S := by rw [hupd]; exact hp
    have hqle : q j ≤ p j := by rw [hqj]; exact h
    have hsegq : ∀ z : ℤ, (q j ≤ z ∧ z ≤ p j) → Function.update q j z ∈ S := by
      intro z hz
      rw [hqj] at hz
      have hqz : Function.update q j z = Function.update p j z := by rw [hq, Function.update_idem]
      rw [hqz]
      apply hseg
      rw [min_eq_right h, max_eq_left h]; exact hz
    have key := (segment_up S j q (p j) hqle hc hcp hsegq).symm
    convert key using 2
    rw [hupd]


end Lattice
end StatMech
