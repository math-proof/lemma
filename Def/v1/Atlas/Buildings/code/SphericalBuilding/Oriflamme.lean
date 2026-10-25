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


namespace Oriflamme

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
         (B : LinearMap.BilinForm k V) (n : ℕ)


/-- A subspace $W \le V$ is **totally isotropic** for $B$ if $B(v, w) = 0$ for all
$v, w \in W$. -/
def IsTotallyIsotropic (W : Submodule k V) : Prop :=
  ∀ v ∈ W, ∀ w ∈ W, B v w = 0

/-- A totally isotropic subspace $W$ is **maximal** if it is not properly contained in any
larger totally isotropic subspace. -/
def IsMaximalTotallyIsotropic (W : Submodule k V) : Prop :=
  IsTotallyIsotropic k V B W ∧
  ∀ W' : Submodule k V, IsTotallyIsotropic k V B W' → W ≤ W' → W = W'

end Oriflamme
