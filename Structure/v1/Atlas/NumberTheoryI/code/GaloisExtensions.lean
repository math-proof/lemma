/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Frobenius
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Galois.Basic
import Abbrev.v1.Atlas.NumberTheoryI.code.GaloisExtensions.Part4
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
