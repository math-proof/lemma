/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Algebra.Set.Closure.eq.N.of.Eq
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Invariant.Basic
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Lemma247
import Def.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part13


noncomputable section

open scoped Pointwise

open NumberField

structure IdealGroupData where
  G : Type*
  I_L : Type*
  I_K : Type*
  [instGroupG : Group G]
  [instFiniteG : Finite G]
  [instCyclicG : IsCyclic G]
  [instCommGroupIL : CommGroup I_L]
  [instCommGroupIK : CommGroup I_K]
  [instAction : MulDistribMulAction G I_L]
  normMap : I_L →* I_K
  extensionMap : I_K →* I_L
  extensionMap_injective : Function.Injective extensionMap
  e₀ : ℕ
  e₀_pos : 0 < e₀
  normImage_index_pos : 0 < normMap.range.index
  extensionMap_range_le_fixedPoints : extensionMap.range ≤ FixedPoints.subgroup G I_L
  cohomNorm_eq : ∀ (I : I_L),
    (haveI := Fintype.ofFinite G; ∏ g : G, g • I) = extensionMap (normMap I)
  augmentation_preimage : ∀ (σ : G), (∀ g : G, g ∈ Subgroup.zpowers σ) →
    ∀ (I : I_L), (haveI := Fintype.ofFinite G; ∏ g : G, g • I) = 1 →
      ∃ J : I_L, σ • J * J⁻¹ = I
  index_fixedPoints_over_range :
    (extensionMap.range.subgroupOf (FixedPoints.subgroup G I_L)).index = e₀

end
