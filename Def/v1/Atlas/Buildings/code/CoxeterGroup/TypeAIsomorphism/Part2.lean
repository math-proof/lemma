/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAIsomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Coxeter.Matrix
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.PresentedGroup
public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAIsomorphism

@[expose] public section

open Equiv Equiv.Perm Function Set


namespace SymmetricCoxeter

/-- Canonical homomorphism $W(A_{n-1}) \to S_{n+1}$ from the type-$A$ Coxeter group to the
symmetric group, sending generators to adjacent transpositions. -/
noncomputable def coxeterToPermHom (n : ℕ) :
    (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin (n + 1)) :=
  PresentedGroup.toGroup (adjTransposition_lift_rels n)

end SymmetricCoxeter
