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
import Abbrev.v1.Atlas.Buildings.code.CoxeterGroup.SignedPermGroup.Part2
set_option maxHeartbeats 800000


namespace SignedPerm

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

end SignedPerm
