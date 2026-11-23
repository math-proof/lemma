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
public import Abbrev.v1.Atlas.NumberTheoryI.code.GaloisExtensions.Part3

@[expose] public section

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

