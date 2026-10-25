/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignedPermGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Perm
import Abbrev.v1.Atlas.Buildings.code.CoxeterGroup.SignedPermGroup
set_option maxHeartbeats 800000


namespace SignedPerm

/-- The permutation action of $S_n$ on the sign group $(\{\pm 1\})^n$ by index permutation,
encoded as a group homomorphism into $\operatorname{MulAut}$. -/
noncomputable def signGroupPermAction (n : ℕ) :
    Equiv.Perm (Fin n) →* MulAut (SignGroup n) where
  toFun σ := {
    toFun := fun ε => ε ∘ σ.symm
    invFun := fun ε => ε ∘ σ
    left_inv := by intro ε; ext i; simp
    right_inv := by intro ε; ext i; simp
    map_mul' := by intros; ext; simp [Pi.mul_apply]
  }
  map_one' := by ext; simp
  map_mul' := by
    intros σ₁ σ₂; ext ε i
    simp [MulAut.mul_apply, Function.comp, Equiv.Perm.mul_def, Equiv.symm_trans_apply]

end SignedPerm
