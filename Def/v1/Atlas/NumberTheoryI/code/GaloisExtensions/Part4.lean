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
public import Structure.v1.Atlas.NumberTheoryI.code.GaloisExtensions

@[expose] public section

open Ideal
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field


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

end SplitsCompletelyCriterion
