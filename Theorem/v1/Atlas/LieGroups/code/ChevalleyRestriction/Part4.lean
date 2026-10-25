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
import Def.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part6


noncomputable section

open scoped TensorProduct

variable (R : Type*) [Field R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]

variable {R 𝔤}

attribute [instance] ChevalleyRestrictionData.instRing
  ChevalleyRestrictionData.instAlgebra

attribute [instance] ChevalleyRestrictionPolyData.instGroupG

theorem chevalley_res_injective_on_invariants
    {k : Type*} [CommRing k]
    {n m : ℕ}
    (G : Type*) [Group G]
    (G_action : G →* (MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k))
    (Res : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin m) k)


    (hRes_kernel_trivial : ∀ (q : MvPolynomial (Fin n) k),
      q ∈ Subalgebra.invariants G G_action → Res q = 0 → q = 0)
    (p₁ p₂ : MvPolynomial (Fin n) k)
    (hp₁ : p₁ ∈ Subalgebra.invariants G G_action)
    (hp₂ : p₂ ∈ Subalgebra.invariants G G_action)
    (h : Res p₁ = Res p₂) :
    p₁ = p₂ := by

  have hker : Res (p₁ - p₂) = 0 := by rw [map_sub, h, sub_self]

  have hinv : (p₁ - p₂) ∈ Subalgebra.invariants G G_action := by
    intro g; simp [map_sub, hp₁ g, hp₂ g]

  have h0 := hRes_kernel_trivial (p₁ - p₂) hinv hker

  exact eq_of_sub_eq_zero h0

theorem chevalley_res_surjective_on_invariants
    {k : Type*} [Field k]
    {𝔤₀ : Type*} [LieRing 𝔤₀] [LieAlgebra k 𝔤₀]
    [LieAlgebra.IsKilling k 𝔤₀] [FiniteDimensional k 𝔤₀]
    {Δ : TriangularDecomposition k 𝔤₀} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := k) (𝔤 := 𝔤₀) wg n m)
    (q : MvPolynomial (Fin m) k)
    (hq : q ∈ Subalgebra.invariants wg.W cpd.W_action) :
    ∃ p : MvPolynomial (Fin n) k,
      p ∈ Subalgebra.invariants cpd.G cpd.G_action ∧ cpd.Res p = q := by


  have hbij := chevalley_restriction_polynomial cpd
  obtain ⟨⟨p, hp⟩, hpq⟩ := hbij.2 ⟨q, hq⟩
  refine ⟨p, hp, ?_⟩
  have := congr_arg Subtype.val hpq
  simpa [ChevalleyRestrictionPolyData.restrictionMapPoly, AlgHom.codRestrict] using this

theorem chevalley_restriction_theorem_10_1
    {k : Type*} [Field k]
    {𝔤₀ : Type*} [LieRing 𝔤₀] [LieAlgebra k 𝔤₀]
    [LieAlgebra.IsKilling k 𝔤₀] [FiniteDimensional k 𝔤₀]
    {Δ : TriangularDecomposition k 𝔤₀} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := k) (𝔤 := 𝔤₀) wg n m) :
    Function.Bijective
      ((cpd.Res.comp (Subalgebra.invariants cpd.G cpd.G_action).val).codRestrict
        (Subalgebra.invariants wg.W cpd.W_action)
        (fun ⟨x, hx⟩ => cpd.Res_maps_invariants x hx)) := by
  constructor
  ·

    intro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ heq
    have h : cpd.Res p₁ = cpd.Res p₂ := by
      have := congr_arg Subtype.val heq
      simpa [AlgHom.codRestrict] using this
    exact Subtype.ext (chevalley_res_injective_on_invariants
      cpd.G cpd.G_action cpd.Res
      cpd.kernel_trivial p₁ p₂ hp₁ hp₂ h)

  ·

    intro ⟨q, hq⟩
    obtain ⟨p, hp_inv, hp_eq⟩ := chevalley_res_surjective_on_invariants cpd q hq
    exact ⟨⟨p, hp_inv⟩, Subtype.ext (by simpa [AlgHom.codRestrict] using hp_eq)⟩

end
