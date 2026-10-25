/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.CompatibleComplexStructures
import Theorem.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import Class.v1.Atlas.GeometryOfManifolds.code.TangentBundleDFS
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Def.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part2
set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


attribute [reducible, instance] IsContractible.ambientAddCommGroup IsContractible.ambientModule


/-- Injectivity of right-composition by a symplectic form: if $\omega(\cdot, J_1\cdot) = \omega(\cdot, J_2\cdot)$
then $J_1 = J_2$, using nondegeneracy of $\omega$. -/
lemma compRight_injective_of_symplectic
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω)
    {J₁ J₂ : V →ₗ[ℝ] V}
    (h : ω.compRight J₁ = ω.compRight J₂) : J₁ = J₂ := by
  ext v
  suffices hw : J₁ v - J₂ v = 0 from sub_eq_zero.mp hw
  apply hω.nondeg
  intro y

  have neg_eq := LinearMap.IsAlt.neg hω.alt (J₁ v - J₂ v) y

  have heq : (ω y) (J₁ v) = (ω y) (J₂ v) := by
    have h1 : (ω.compRight J₁) y = (ω.compRight J₂) y := by rw [h]
    have h2 : ((ω.compRight J₁) y) v = ((ω.compRight J₂) y) v := by rw [h1]
    simp only [LinearMap.BilinForm.compRight_apply] at h2
    exact h2

  have hzero : (ω y) (J₁ v - J₂ v) = 0 := by rw [map_sub]; linarith

  linarith

/-- **Polar-decomposition style retraction** onto compatible complex structures: there exists a
map $\mathrm{polar} : \mathrm{BilinForm}(V) \to \mathrm{End}(V)$ producing a compatible $J$ for
each form, and acting as the identity on graphs $\omega(\cdot, J\cdot)$ of compatible $J$. -/
theorem polar_decomposition_compatible_J
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω) :


    ∃ (polar : LinearMap.BilinForm ℝ V → V →ₗ[ℝ] V),

      (∀ g, IsCompatibleComplexStr ω (polar g)) ∧


      (∀ (J : V →ₗ[ℝ] V), IsCompatibleComplexStr ω J →
        polar (ω.compRight J) = J) := by
  classical

  obtain ⟨J₀, hJ₀⟩ := exists_compatible_complex_structure hω


  let polar : LinearMap.BilinForm ℝ V → V →ₗ[ℝ] V := fun g =>
    if h : ∃ J : V →ₗ[ℝ] V, IsCompatibleComplexStr ω J ∧ ω.compRight J = g then
      h.choose
    else
      J₀
  refine ⟨polar, ?_, ?_⟩

  · intro g
    simp only [polar]
    split_ifs with h
    · exact h.choose_spec.1
    · exact hJ₀

  · intro J hJ
    simp only [polar]


    have hex : ∃ J' : V →ₗ[ℝ] V, IsCompatibleComplexStr ω J' ∧ ω.compRight J' = ω.compRight J :=
      ⟨J, hJ, rfl⟩
    rw [dif_pos hex]

    have hJ'_spec := hex.choose_spec

    exact compRight_injective_of_symplectic hω hJ'_spec.2


