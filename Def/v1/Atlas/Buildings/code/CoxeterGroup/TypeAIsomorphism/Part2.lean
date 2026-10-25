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
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAIsomorphism
open Equiv Equiv.Perm Function Set


namespace SymmetricCoxeter

/-- Canonical homomorphism $W(A_{n-1}) \to S_{n+1}$ from the type-$A$ Coxeter group to the
symmetric group, sending generators to adjacent transpositions. -/
noncomputable def coxeterToPermHom (n : ℕ) :
    (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin (n + 1)) :=
  PresentedGroup.toGroup (adjTransposition_lift_rels n)

end SymmetricCoxeter
