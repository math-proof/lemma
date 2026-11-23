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
public import Def.v1.Atlas.Buildings.code.SphericalBuilding.Oriflamme

@[expose] public section


namespace Oriflamme

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
         (B : LinearMap.BilinForm k V) (n : ℕ)


/-- The two $\mathrm{SO}(n, n)$-orbits of maximal isotropic $n$-subspaces, indexed by `Bool`
($V_1$ and $V_2$ in the oriflamme construction). -/
abbrev MaxIsotropicClass := Bool


end Oriflamme
