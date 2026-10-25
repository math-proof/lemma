/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraCorollaries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.LieGroups.code.MaximalQuotients
import Def.v1.Atlas.LieGroups.code.HarishChandraCorollaries
universe u_hc_bim


noncomputable section

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

end
