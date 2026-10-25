/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA211417_supercongruence_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.FC.OeisA211417_supercongruence_solution


namespace OeisA211417

open Nat Int Finset

def unitIndexEquiv (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
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

end OeisA211417
