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
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.Oriflamme.Part2


namespace Oriflamme

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
         (B : LinearMap.BilinForm k V) (n : ℕ)


/-- The **isometry group** $O(V, B)$ of the bilinear form: all $k$-linear automorphisms of $V$
preserving $B$. -/
def OriflammeIsometryGroup : Set (V ≃ₗ[k] V) :=
  { g | ∀ v₁ v₂, B (g v₁) (g v₂) = B v₁ v₂ }

/-- The oriflamme building is **strongly transitive** under $\mathrm{SO}(V, B)$ if any pair
of frame/chamber data in two apartments can be mapped one to the other by an isometry. -/
def SO_StronglyTransitive (X : OriflammeComplex k V B n)
    (bldg : OriflammeIsBuilding k V B n X) : Prop :=
  ∀ (F₁ F₂ : OriflammeFrame k V B n),
    F₁ ∈ bldg.apartments → F₂ ∈ bldg.apartments →
    ∀ C₁ ∈ OriflammeApartment k V B n X F₁,
    ∀ C₂ ∈ OriflammeApartment k V B n X F₂,
    ∃ g ∈ OriflammeIsometryGroup k V B,
      (∀ ib, (F₁.lines ib).map g.toLinearMap = F₂.lines ib) ∧
      (∀ W ∈ C₁, ∃ W' ∈ C₂, W.map g.toLinearMap = W')


end Oriflamme
