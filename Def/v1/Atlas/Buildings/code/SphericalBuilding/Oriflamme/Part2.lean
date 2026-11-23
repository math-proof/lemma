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
public import Theorem.Submodule.OfEq.eq.M.of.Eq
public import Theorem.Submodule.Any_EqAndAll_Eq_V.of.IsSubspaceIsometry.EqOrthogonalBilinFormTop_Bot.All_Eq
public import Abbrev.v1.Atlas.Buildings.code.SphericalBuilding.Oriflamme

@[expose] public section

namespace Oriflamme

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
         (B : LinearMap.BilinForm k V) (n : ℕ)


/-- An **oriflamme vertex**: a nonzero totally isotropic subspace whose dimension is **not**
$n - 1$ (this dimension is excluded by the oriflamme construction). -/
def IsOriflammeVertex (W : Submodule k V) : Prop :=
  IsTotallyIsotropic k V B W ∧ W ≠ ⊥ ∧ Module.finrank k W ≠ n - 1

/-- **Oriflamme incidence**: two oriflamme vertices $x, y$ are incident if $x \subsetneq y$,
$y \subsetneq x$, or both are $n$-dimensional with $\dim(x \cap y) = n - 1$. -/
def OriflammeIncident (x y : Submodule k V) : Prop :=
  x < y ∨ y < x ∨
  (Module.finrank k x = n ∧ Module.finrank k y = n ∧
   Module.finrank k ↥(x ⊓ y) = n - 1)

end Oriflamme
