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
public import Structure.v1.Atlas.Buildings.code.SphericalBuilding.Oriflamme

@[expose] public section

namespace Oriflamme

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
         (B : LinearMap.BilinForm k V) (n : ℕ)


/-- The **apartment** of the oriflamme complex $X$ associated to a frame $F$: the simplices
all of whose vertices are sums of frame lines. -/
def OriflammeApartment (X : OriflammeComplex k V B n) (F : OriflammeFrame k V B n) :
    Set (Finset (Submodule k V)) :=
  { σ ∈ X.simplices |
    ∀ W ∈ σ, ∃ S : Finset (Fin n × Bool),
      W = ⨆ ib ∈ S, F.lines ib }


end Oriflamme
