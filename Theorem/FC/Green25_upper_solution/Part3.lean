/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.Green25_upper_solution.Part3
open Asymptotics Filter Finset


namespace Green25

lemma digitVector_encode (Q m : ℕ) [NeZero (Q ^ m)] (v : Fin m → Fin Q) :
    digitVector Q m (encodeVector v) = v := by
  apply finFunctionFinEquiv.injective
  apply Fin.ext
  have h := (finFunctionFinEquiv v).isLt
  simp only [digitVector, encodeVector, Equiv.apply_symm_apply, Fin.ofNat,
    Nat.add_sub_cancel]
  exact Nat.mod_eq_of_lt h

lemma encodeVector_mem (Q m : ℕ) (v : Fin m → Fin Q) :
    encodeVector v ∈ Icc 1 (Q ^ m) := by
  simp only [Finset.mem_Icc, encodeVector]
  constructor <;> omega

lemma encode_digitVector (Q m x : ℕ) [NeZero (Q ^ m)]
    (hx : x ∈ Icc 1 (Q ^ m)) : encodeVector (digitVector Q m x) = x := by
  simp only [Finset.mem_Icc] at hx
  simp only [encodeVector, digitVector, Equiv.apply_symm_apply, Fin.ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

end Green25
