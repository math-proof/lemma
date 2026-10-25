/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA211417_supercongruence_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.FC.OeisA211417_supercongruence_solution.Part2


namespace OeisA211417

open Nat Int Finset

noncomputable def blockProd (p k t : ℕ) : ℕ :=
  ∏ i : unitIndex p k, (t * p ^ k + i.val)

def unitIndexNeg (p k : ℕ) (hp0 : 0 < p) (hk : 0 < k) :
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

end OeisA211417
