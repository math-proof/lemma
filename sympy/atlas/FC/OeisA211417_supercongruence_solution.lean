/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA211417_supercongruence_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace OeisA211417


def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

open Nat Int Finset

private def unitProd (p n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, if p ∣ i + 1 then 1 else i + 1

private def unitIndex (p k : ℕ) := {i : Fin (p ^ k) // ¬p ∣ i.val}

private noncomputable instance unitIndexFintype (p k : ℕ) : Fintype (unitIndex p k) := by
  unfold unitIndex
  infer_instance

private def unitIndexEquiv (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    unitIndex p k ≃ (ZMod (p ^ k))ˣ := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine
    { toFun := fun i =>
        ZMod.unitOfCoprime i.val (hp.coprime_pow_of_not_dvd i.prop)
      invFun := fun u => ⟨⟨(u : ZMod (p ^ k)).val, ZMod.val_lt _⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro hdiv
    have hc := ZMod.val_coe_unit_coprime u
    apply hp.not_dvd_one
    rw [← hc.gcd_eq_one]
    exact Nat.dvd_gcd hdiv (dvd_pow_self p hk.ne')
  · intro i
    apply Subtype.ext
    apply Fin.ext
    dsimp
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.val.isLt]
  · intro u
    apply Units.ext
    dsimp
    exact ZMod.natCast_zmod_val (u : ZMod (p ^ k))

private noncomputable instance unitIndexDecidableEq (p k : ℕ) :
    DecidableEq (unitIndex p k) := Classical.decEq _

private noncomputable def blockProd (p k t : ℕ) : ℕ :=
  ∏ i : unitIndex p k, (t * p ^ k + i.val)

private def unitIndexNeg (p k : ℕ) (hp0 : 0 < p) (hk : 0 < k) :
    unitIndex p k ≃ unitIndex p k := by
  let q := p ^ k
  have hq : 0 < q := pow_pos hp0 k
  have hpq : p ∣ q := dvd_pow_self p hk.ne'
  refine
    { toFun := fun i => ⟨⟨q - i.1.1, by
          have hi0 : 0 < i.1.1 := by
            by_contra h
            apply i.prop
            have hz : i.1.1 = 0 := by omega
            simpa [hz]
          omega⟩, ?_⟩
      invFun := fun i => ⟨⟨q - i.1.1, by
          have hi0 : 0 < i.1.1 := by
            by_contra h
            apply i.prop
            have hz : i.1.1 = 0 := by omega
            simpa [hz]
          omega⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro hdiv
    apply i.prop
    have hsub := Nat.dvd_sub hpq hdiv
    change p ∣ q - (q - i.1.1) at hsub
    rw [Nat.sub_sub_self (by omega)] at hsub
    exact hsub
  · intro hdiv
    apply i.prop
    have hsub := Nat.dvd_sub hpq hdiv
    change p ∣ q - (q - i.1.1) at hsub
    rw [Nat.sub_sub_self (by omega)] at hsub
    exact hsub
  · intro i
    apply Subtype.ext
    apply Fin.ext
    change q - (q - i.1.1) = i.1.1
    exact Nat.sub_sub_self (by omega)
  · intro i
    apply Subtype.ext
    apply Fin.ext
    change q - (q - i.1.1) = i.1.1
    exact Nat.sub_sub_self (by omega)
