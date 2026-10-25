/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParitySign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.ParitySign


namespace CoxeterSystem

open List

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- Parity sign homomorphism $\varepsilon : W \to \{\pm 1\}$ defined by
$\varepsilon(w) = (-1)^{\ell(w)}$; well-defined because $\ell$ is well-defined modulo $2$
under multiplication. -/
noncomputable def paritySign : W →* ℤˣ where
  toFun w := (-1 : ℤˣ) ^ cs.length w
  map_one' := by simp [cs.length_one]
  map_mul' w₁ w₂ := by
    have h := cs.length_mul_mod_two w₁ w₂
    have heq := neg_one_units_pow_eq_of_mod_two_eq h
    rw [heq]
    ext
    change ((-1 : ℤ) ^ (cs.length w₁ + cs.length w₂)) =
      ((-1 : ℤ) ^ cs.length w₁) * ((-1 : ℤ) ^ cs.length w₂)
    exact pow_add (-1 : ℤ) _ _

end CoxeterSystem
