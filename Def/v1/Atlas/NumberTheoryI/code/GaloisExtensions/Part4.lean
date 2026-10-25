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
import Structure.v1.Atlas.NumberTheoryI.code.GaloisExtensions
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
