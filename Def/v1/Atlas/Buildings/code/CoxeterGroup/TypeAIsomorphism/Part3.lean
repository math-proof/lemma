/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAIsomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.PresentedGroup
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAIsomorphism.Part2
open Equiv Equiv.Perm Function Set


namespace SymmetricCoxeter

/-- Group isomorphism $S_{n+1} \cong W(A_{n-1})$, the inverse of `coxeterToPermHom`. -/
noncomputable def permCoxeterMulEquiv (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) ≃* (CoxeterMatrix.A n).Group :=
  (MulEquiv.ofBijective (coxeterToPermHom n)
    ⟨coxeterToPermHom_injective n, coxeterToPermHom_surjective n⟩).symm

/-- The type-$A_{n-1}$ Coxeter system on the symmetric group $S_{n+1}$. -/
noncomputable def permCoxeterSystem (n : ℕ) :
    CoxeterSystem (CoxeterMatrix.A n) (Equiv.Perm (Fin (n + 1))) :=
  ⟨permCoxeterMulEquiv n⟩

end SymmetricCoxeter
