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
import Def.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part2


noncomputable section

open scoped TensorProduct

variable (R : Type*) [Field R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]

variable {R 𝔤}

attribute [instance] ChevalleyRestrictionData.instRing
  ChevalleyRestrictionData.instAlgebra

omit [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤] in
theorem chevalley_restriction_injective_aux
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (crd : ChevalleyRestrictionData Δ wg) :
    Function.Injective crd.restrictionMap := by
  intro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ heq
  have h_res : crd.restrictionAlgHom f₁ = crd.restrictionAlgHom f₂ := by
    have := congr_arg Subtype.val heq
    simpa [ChevalleyRestrictionData.restrictionMap, AlgHom.codRestrict] using this
  have h_eval_h : ∀ h : Δ.𝔥, crd.eval𝔤 f₁ (h : 𝔤) = crd.eval𝔤 f₂ (h : 𝔤) := by
    intro h
    rw [← crd.eval_restriction_compat f₁ h, ← crd.eval_restriction_compat f₂ h, h_res]
  have h_eval_all : ∀ x : 𝔤, crd.eval𝔤 f₁ x = crd.eval𝔤 f₂ x :=
    crd.adInvariant_eval_determined_by_h f₁ f₂ hf₁ hf₂ h_eval_h
  have h_eq : f₁ = f₂ := crd.eval𝔤_injective (funext h_eval_all)
  exact Subtype.ext h_eq

omit [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤] in
theorem chevalley_restriction_surjective_aux
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (crd : ChevalleyRestrictionData Δ wg) :
    Function.Surjective crd.restrictionMap := by
  intro ⟨p, hp⟩
  obtain ⟨f, hf_inv, hf_eval⟩ := crd.trace_function_surjectivity p hp
  have h_eq : crd.restrictionAlgHom f = p :=
    crd.eval𝔥_injective (funext hf_eval)
  exact ⟨⟨f, hf_inv⟩, Subtype.ext h_eq⟩

theorem chevalley_restriction_injective
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ} :
    Function.Injective (chevalleyRestrictionData wg).restrictionMap :=
  chevalley_restriction_injective_aux (chevalleyRestrictionData wg)

theorem chevalley_restriction_surjective
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ} :
    Function.Surjective (chevalleyRestrictionData wg).restrictionMap :=
  chevalley_restriction_surjective_aux (chevalleyRestrictionData wg)

theorem chevalley_restriction_bijective
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ} :
    Function.Bijective (chevalleyRestrictionData wg).restrictionMap :=
  ⟨chevalley_restriction_injective, chevalley_restriction_surjective⟩

end
