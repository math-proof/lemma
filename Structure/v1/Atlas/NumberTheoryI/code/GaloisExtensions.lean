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
public import Abbrev.v1.Atlas.NumberTheoryI.code.GaloisExtensions.Part4
public section

open Ideal
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field


section SplittingCriterion

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

structure UnramifiedFrobeniusData (P : Ideal B) (q : ℕ) : Prop where
  unique_exists : ∃! σ : G, IsFrobeniusElement G σ P q
  mem_stabilizer : frobeniusElement G P q unique_exists ∈ MulAction.stabilizer G P
  generates_stabilizer : ∀ g, g ∈ MulAction.stabilizer G P →
    ∃ n : ℕ, g = frobeniusElement G P q unique_exists ^ n

end SplittingCriterion
