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
import Structure.v1.Atlas.LieGroups.code.ChevalleyRestriction


noncomputable section

open scoped TensorProduct

variable (R : Type*) [Field R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]

variable {R 𝔤}

attribute [instance] ChevalleyRestrictionData.instRing
  ChevalleyRestrictionData.instAlgebra

noncomputable def killingFormDualIso
    {R : Type*} [Field R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) :
    Δ.𝔥 ≃ₗ[R] (Δ.𝔥 →ₗ[R] R) := by
  haveI : Δ.𝔥.IsCartanSubalgebra := Δ.is_cartan
  exact LieAlgebra.IsKilling.cartanEquivDual Δ.𝔥

noncomputable def TriangularDecomposition.projectToH
    {R : Type*} [Field R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (x : 𝔤) : Δ.𝔥 :=
  (Δ.decomp_exists x).choose_spec.choose

noncomputable def chevalleyEval𝔥
    {R : Type*} [Field R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (p : UniversalEnvelopingAlgebra R Δ.𝔥) (h : Δ.𝔥) : R :=
  evalWeight Δ (killingFormDualIso Δ h) p

noncomputable def chevalleyEval𝔤
    {R : Type*} [Field R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (f : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))) (x : 𝔤) : R :=
  chevalleyEval𝔥 Δ (HarishChandraAlgHom Δ f) (Δ.projectToH x)

noncomputable def chevalleyRestrictionData
    {Δ : TriangularDecomposition R 𝔤} (wg : WeylGroupData Δ) :
    ChevalleyRestrictionData Δ wg where
  S𝔤 := ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
  instRing := inferInstance
  instAlgebra := inferInstance
  adInvariant := ⊤
  restrictionAlgHom := HarishChandraAlgHom Δ
  algActionOnS𝔤 := 1
  restriction_equivariant := fun w f => by
    simp only [MonoidHom.one_apply, AlgEquiv.one_apply]
    exact (harishChandra_maps_to_W_invariants Δ wg f w).symm
  adInvariant_W_fixed := fun w f _ => by
    simp only [MonoidHom.one_apply, AlgEquiv.one_apply]
  eval𝔤 := chevalleyEval𝔤 Δ
  eval𝔥 := chevalleyEval𝔥 Δ
  eval𝔤_injective := by
    intro f₁ f₂ heval
    have h_eval_h : ∀ h : Δ.𝔥, chevalleyEval𝔥 Δ (HarishChandraAlgHom Δ f₁) h =
        chevalleyEval𝔥 Δ (HarishChandraAlgHom Δ f₂) h := by
      intro h
      have := congr_fun heval (h : 𝔤)
      simp only [chevalleyEval𝔤, Δ.projectToH_of_mem_h h] at this
      exact this
    have h_hc_eq : HarishChandraAlgHom Δ f₁ = HarishChandraAlgHom Δ f₂ := by
      apply evalWeight_separates
      intro wt
      have h_surj := (killingFormDualIso Δ).surjective wt
      obtain ⟨h, rfl⟩ := h_surj
      exact h_eval_h h
    exact harishChandra_center_injective Δ wg f₁ f₂ (by
      show HarishChandraMap Δ (f₁ : UniversalEnvelopingAlgebra R 𝔤) =
           HarishChandraMap Δ (f₂ : UniversalEnvelopingAlgebra R 𝔤)

      exact h_hc_eq)
  eval𝔥_injective := by
    intro p₁ p₂ heval
    apply evalWeight_separates
    intro wt
    obtain ⟨h, rfl⟩ := (killingFormDualIso Δ).surjective wt
    exact congr_fun heval h
  eval_restriction_compat := fun f h => by
    simp only [chevalleyEval𝔤, chevalleyEval𝔥]
    rw [Δ.projectToH_of_mem_h h]
  adInvariant_eval_determined_by_h := fun f₁ f₂ _ _ h_agree x => by
    simp only [chevalleyEval𝔤] at h_agree ⊢

    simp only [Δ.projectToH_of_mem_h] at h_agree

    exact h_agree (Δ.projectToH x)
  trace_function_surjectivity := fun p hp => by
    obtain ⟨c, hc⟩ := (harishChandra_bijectivity Δ wg).2 p hp
    refine ⟨c, Algebra.mem_top, fun h => ?_⟩
    simp only [chevalleyEval𝔥]
    have : (HarishChandraAlgHom Δ) c = p := hc
    rw [this]

end
