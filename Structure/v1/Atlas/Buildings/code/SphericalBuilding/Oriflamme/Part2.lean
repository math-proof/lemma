/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Determinant
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Lemma.Submodule.OfEq.eq.M.of.Eq
import Lemma.Submodule.Any_EqAndAll_Eq_V.of.IsSubspaceIsometry.EqOrthogonalBilinFormTop_Bot.All_Eq
import Def.v1.Atlas.Buildings.code.SphericalBuilding.Oriflamme.Part3


namespace Oriflamme

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
         (B : LinearMap.BilinForm k V) (n : ℕ)


/-- Witness that the oriflamme complex $X$ is a building of type $D_n$: a family of apartments
satisfying the common-apartment and apartment-exchange axioms. -/
structure OriflammeIsBuilding (X : OriflammeComplex k V B n) where
  apartments : Set (OriflammeFrame k V B n)
  common_apartment : ∀ σ₁ ∈ X.simplices, ∀ σ₂ ∈ X.simplices,
    ∃ F ∈ apartments, σ₁ ∈ OriflammeApartment k V B n X F ∧
      σ₂ ∈ OriflammeApartment k V B n X F
  apartment_exchange : ∀ F₁ ∈ apartments, ∀ F₂ ∈ apartments,
    (∃ C ∈ OriflammeApartment k V B n X F₁,
      C ∈ OriflammeApartment k V B n X F₂) →
    ∃ f : Submodule k V → Submodule k V,
      (∀ σ ∈ OriflammeApartment k V B n X F₁,
        σ.image f ∈ OriflammeApartment k V B n X F₂) ∧
      (∀ W, (∃ σ ∈ OriflammeApartment k V B n X F₁ ∩
        OriflammeApartment k V B n X F₂, W ∈ σ) →
        f W = W)

end Oriflamme
