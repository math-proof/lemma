/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Frobenius
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Group.Conj
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.Galois.Basic
@[expose] public section

open Ideal
open scoped Pointwise


abbrev IsLeftGModule (G : Type*) (M : Type*) [Group G] [AddCommGroup M]
    [DistribMulAction G M] : Prop := True

