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
import Abbrev.v1.Atlas.NumberTheoryI.code.GaloisExtensions.Part3
open Ideal
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field


noncomputable def decompositionQuotientInertiaEquiv
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] :
    MulAction.stabilizer G Q ⧸ (Q.inertia G).subgroupOf (MulAction.stabilizer G Q) ≃*
      ((B ⧸ Q) ≃ₐ[A ⧸ p] (B ⧸ Q)) :=
  Ideal.Quotient.stabilizerQuotientInertiaEquiv G p Q

@[deprecated decompositionQuotientInertiaEquiv (since := "2025-05-04")]
noncomputable def exact_sequence_inertia_decomposition
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] :
    MulAction.stabilizer G Q ⧸ (Q.inertia G).subgroupOf (MulAction.stabilizer G Q) ≃*
      ((B ⧸ Q) ≃ₐ[A ⧸ p] (B ⧸ Q)) :=
  decompositionQuotientInertiaEquiv G Q

def IsFrobeniusElement (σ : G) (Q : Ideal B) (q : ℕ) : Prop :=
  ∀ x : B, (σ • x - x ^ q) ∈ Q

noncomputable def frobeniusElement (Q : Ideal B) (q : ℕ)
    (hexists : ∃! σ : G, IsFrobeniusElement G σ Q q) : G :=
  hexists.choose

noncomputable def frobeniusClass (Q : Ideal B) (q : ℕ)
    (hexists : ∃! σ : G, IsFrobeniusElement G σ Q q) : ConjClasses G :=
  ConjClasses.mk (frobeniusElement G Q q hexists)

