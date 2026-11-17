/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.Invariant.Basic


public noncomputable section

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
