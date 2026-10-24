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

set_option maxHeartbeats 800000

namespace SignedPerm

/-- The sign group $(\{\pm 1\})^n$ realized multiplicatively as $\operatorname{Fin}(n) \to (\mathbb{Z}/2)^\times$. -/
abbrev SignGroup (n : ℕ) := Fin n → Multiplicative (ZMod 2)

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

/-- The signed permutation group (hyperoctahedral group) $S_n^\pm = (\{\pm 1\})^n \rtimes S_n$,
the Coxeter group of type $C_n$ (Section 10.2). -/
abbrev SignedPermGroup (n : ℕ) := SignGroup n ⋊[signGroupPermAction n] Equiv.Perm (Fin n)

/-- As a set, $S_n^\pm$ is in bijection with $(\{\pm 1\})^n \times S_n$. -/
def signedPermGroupEquivProd (n : ℕ) :
    SignedPermGroup n ≃ (SignGroup n × Equiv.Perm (Fin n)) where
  toFun x := (x.left, x.right)
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- The generator $\varepsilon_j \in (\{\pm 1\})^n$ that flips the sign at coordinate $j$ only. -/
def signChangeAt (n : ℕ) (j : Fin n) : SignGroup n :=
  Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 2))

/-- The Coxeter generators of $S_{n+1}^\pm$: the $n$ adjacent transpositions
plus the sign flip at the last coordinate. -/
noncomputable def generators (n : ℕ) : Set (SignedPermGroup (n + 1)) :=
  (Set.range fun (i : Fin n) =>
    (SemidirectProduct.inr (Equiv.swap (Fin.castSucc i) (Fin.succ i))
      : SignedPermGroup (n + 1))) ∪
  {SemidirectProduct.inl (signChangeAt (n + 1) (Fin.last n))}
