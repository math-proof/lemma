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

open Ideal
open scoped Pointwise

abbrev IsLeftGModule (G : Type*) (M : Type*) [Group G] [AddCommGroup M]
    [DistribMulAction G M] : Prop := True

@[reducible]
def galois_gmodule_fractional_ideals :
    MulSemiringAction G (Ideal B) :=
  inferInstance

abbrev decompositionGroup (Q : Ideal B) : Subgroup G :=
  MulAction.stabilizer G Q

noncomputable def residueField_surjection
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] :
    MulAction.stabilizer G Q ⧸ (Q.inertia G).subgroupOf (MulAction.stabilizer G Q) ≃*
      ((B ⧸ Q) ≃ₐ[A ⧸ p] (B ⧸ Q)) :=
  Ideal.Quotient.stabilizerQuotientInertiaEquiv G p Q

attribute [local instance] Ideal.Quotient.field

abbrev inertiaGroup (Q : Ideal B) : Subgroup G :=
  Q.inertia G

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

noncomputable abbrev artinSymbol (Q : Ideal B) (q : ℕ)
    (hexists : ∃! σ : G, IsFrobeniusElement G σ Q q) : G :=
  frobeniusElement G Q q hexists

end ArtinSymbolDef

section SplittingCriterion

variable {B : Type*} [CommRing B]
  (G : Type*) [Group G] [MulSemiringAction G B]

structure UnramifiedFrobeniusData (P : Ideal B) (q : ℕ) : Prop where
  unique_exists : ∃! σ : G, IsFrobeniusElement G σ P q
  mem_stabilizer : frobeniusElement G P q unique_exists ∈ MulAction.stabilizer G P
  generates_stabilizer : ∀ g, g ∈ MulAction.stabilizer G P →
    ∃ n : ℕ, g = frobeniusElement G P q unique_exists ^ n

end UnramifiedFrobeniusDataDef

section SplitsCompletelyCriterion

open Ideal

variable {A B : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  {p : Ideal A} [p.IsMaximal]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

noncomputable def artinMap
    {S : Set (Ideal A)}
    (artinSymbolPrime : {𝔭 : Ideal A // 𝔭.IsPrime ∧ 𝔭 ∉ S} → G) :
    FreeAbelianGroup {𝔭 : Ideal A // 𝔭.IsPrime ∧ 𝔭 ∉ S} →+ Additive G :=
  FreeAbelianGroup.lift (fun 𝔭 => Additive.ofMul (artinSymbolPrime 𝔭))
