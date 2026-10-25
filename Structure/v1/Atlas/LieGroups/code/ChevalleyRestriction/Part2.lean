/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
import Lemma.Int.Any_All_Eq.of.LeKer_Ker.Surjective
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Def.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part3


noncomputable section

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
