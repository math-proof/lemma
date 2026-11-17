/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Determinant
public import Def.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
public import Structure.v1.Atlas.Buildings.code.SphericalBuilding.Oriflamme.Part2

@[expose] public section

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
