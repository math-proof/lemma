/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohEquivalenceProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.AlgebraicGeometry.Modules.Tilde

set_option maxHeartbeats 4000000

namespace QCohEquivalenceProof

open Submodule

/-- Construct an inverse linear map from `N` to `M` assuming `η : M → N`
becomes bijective after localization at every maximal ideal — used to invert
maps via local data. -/
noncomputable def inverse_from_local_data {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (η : M →ₗ[R] N)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Function.Bijective (LocalizedModule.map P.primeCompl η)) :
    N →ₗ[R] M :=
  (LinearEquiv.ofBijective η (bijective_of_localized_maximal η h)).symm

open CategoryTheory AlgebraicGeometry

/-- Restricting the tilde functor to its essential image yields an equivalence
`Mod R ≃ EssImage(tilde)`, a step toward the equivalence with `QCoh(Spec R)`. -/
noncomputable def qcoh_mod_equivalence (R : CommRingCat.{u}) :
    ModuleCat.{u} R ≌ (tilde.functor R).EssImageSubcategory :=
  (tilde.functor R).toEssImage.asEquivalence

/-- `M̃` is quasi-coherent for every `R`-module `M` (Cor 16). -/
instance qcoh_tilde_isQuasicoherent {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent :=
  inferInstance
