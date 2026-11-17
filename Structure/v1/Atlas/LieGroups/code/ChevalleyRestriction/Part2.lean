/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Weights.Killing
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Def.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part3


public noncomputable section

open scoped TensorProduct

variable (R : Type*) [Field R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]

variable {R 𝔤}

attribute [instance] ChevalleyRestrictionData.instRing
  ChevalleyRestrictionData.instAlgebra

structure IsComplexReflection {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (g : V ≃ₗ[k] V) : Prop where
  rank_eq_one : Module.finrank k (LinearMap.range ((g : V →ₗ[k] V) - LinearMap.id)) = 1
  ne_id : g ≠ LinearEquiv.refl k V

structure IsComplexReflectionGroup {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (G : Type*) [Group G] [Fintype G]
    (ρ : G →* V ≃ₗ[k] V) : Prop where
  generated_by_reflections :
    ∀ g : G, ∃ (n : ℕ) (reflections : Fin n → G),
      (∀ i, IsComplexReflection (ρ (reflections i))) ∧
      g = (List.ofFn reflections).prod

end
