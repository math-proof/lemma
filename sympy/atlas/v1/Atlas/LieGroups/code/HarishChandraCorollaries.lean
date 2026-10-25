/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraCorollaries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.MaximalQuotients

universe u_hc_bim

noncomputable section

def HomAdEquivariant.postcomp
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {V : Type*} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    {N M : LieBimodule R 𝔤}
    (π : N.carrier →ₗ[R] M.carrier)
    (hπ_left : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (n : N.carrier),
      π (N.leftAction u n) = M.leftAction u (π n))
    (hπ_right : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (n : N.carrier),
      π (N.rightAction u n) = M.rightAction u (π n)) :
    HomAdEquivariant V N →ₗ[R] HomAdEquivariant V M where
  toFun f := ⟨π.comp f.val, by
    intro x v
    simp only [LinearMap.comp_apply]
    rw [f.property x v]
    show π (N.adjointAction x (f.val v)) = M.adjointAction x (π (f.val v))
    simp only [LieBimodule.adjointAction, LinearMap.sub_apply]
    rw [← hπ_left, ← hπ_right, map_sub]⟩
  map_add' f g := by
    ext v
    simp [LinearMap.comp_apply, LinearMap.add_apply]
  map_smul' c f := by
    ext v
    simp [LinearMap.comp_apply, LinearMap.smul_apply]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]

/-- Part (i) of Harish-Chandra corollary 14.5. Opaque API for Complex wrappers. -/
theorem corollary_14_5_i
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    (M : LieBimodule.{_, _, u_hc_bim} ℂ 𝔤)
    (hirr : M.IsIrreducible)
    (hlocfin : IsHarishChandraBimodule M) :
    ∃ (χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ)
      (V : Type u_hc_bim) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : LieRingModule 𝔤 V) (_ : LieModule ℂ 𝔤 V)
      (_ : Module.Finite ℂ V)
      (_ : LieModule.IsIrreducible ℂ 𝔤 V),
      ∃ (surj : TensorProduct ℂ V (MaximalQuotient χ) →ₗ[ℂ] M.carrier),
        Function.Surjective surj ∧
        (∀ (x : 𝔤) (t : TensorProduct ℂ V (MaximalQuotient χ)),
          surj ((tensorBimodule (LieBimodule.trivial V) χ).adjointAction x t) =
          M.adjointAction x (surj t)) := by
  sorry

/-- Corollary 14.4: tensor with a maximal quotient is admissible. -/
theorem corollary_14_4
    [LieAlgebra.IsSemisimple ℂ 𝔤] [Module.Finite ℂ 𝔤]
    (Δ : TriangularDecomposition ℂ 𝔤)
    (V : LieBimodule ℂ 𝔤)
    [Module.Finite ℂ V.carrier]
    (χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ) :
    IsAdmissibleBimodule (tensorBimodule V χ) := by
  sorry

/-- Quotients of admissible bimodules by equivariant surjections remain Hom-finite. -/
theorem hc_quotient_admissible
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    (N M : LieBimodule ℂ 𝔤)
    (hN : IsAdmissibleBimodule N)
    (f : N.carrier →ₗ[ℂ] M.carrier)
    (hf_surj : Function.Surjective f)
    (hf_equivar : ∀ (x : 𝔤) (n : N.carrier),
      f (N.adjointAction x n) = M.adjointAction x (f n)) :
    ∀ (W : Type 0) [AddCommGroup W] [Module ℂ W] [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
      [Module.Finite ℂ W] (_ : LieModule.IsIrreducible ℂ 𝔤 W),
      Module.Finite ℂ (HomAdEquivariant W M) := by
  sorry

