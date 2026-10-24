/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.Topology.KrullDimension

set_option maxHeartbeats 400000

noncomputable section

open Set

/-- A topological space has the *proper closed finite* property if every proper closed subset
is finite (characteristic of a one-dimensional space such as an irreducible curve). -/
def ProperClosedFinite (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ s : Set X, IsClosed s → s ≠ Set.univ → s.Finite

/-- Any injective map from a `T1` space to a space whose proper closed subsets are finite is
automatically continuous. -/
theorem continuous_of_injective_of_T1_properClosedFinite
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] (hY : ProperClosedFinite Y)
    {f : X → Y} (hf_inj : Function.Injective f) :
    Continuous f := by
  rw [continuous_def]
  intro U hU
  by_cases hUe : U = ∅
  · simp [hUe]
  · have hUc_ne : Uᶜ ≠ Set.univ := by
      intro h; apply hUe; simp at h; exact h
    have hUc_finite : Uᶜ.Finite := hY Uᶜ hU.isClosed_compl hUc_ne
    have hpre_finite : (f ⁻¹' Uᶜ).Finite := hUc_finite.preimage hf_inj.injOn
    rw [Set.preimage_compl] at hpre_finite
    have hclosed : IsClosed (f ⁻¹' U)ᶜ := hpre_finite.isClosed
    have := hclosed.isOpen_compl
    simp at this
    exact this

/-- Promote an equivalence between two `T1` spaces with the proper-closed-finite property to a
homeomorphism. -/
def Homeomorph.ofEquivProperClosedFinite
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] [T1Space Y]
    (hX : ProperClosedFinite X) (hY : ProperClosedFinite Y)
    (e : X ≃ Y) : X ≃ₜ Y :=
  { toEquiv := e
    continuous_toFun := continuous_of_injective_of_T1_properClosedFinite hY e.injective
    continuous_invFun := continuous_of_injective_of_T1_properClosedFinite hX e.symm.injective }

universe u
