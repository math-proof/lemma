/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CompatibleComplexStructures.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.GeometryOfManifolds.code.SymplecticStandardBasis
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticStandardBasis
set_option autoImplicit false

open Module FiniteDimensional


namespace SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A linear map $J: V \to V$ is a complex structure iff $J^2 = -I$. -/
structure IsComplexStructure (J : V →ₗ[ℝ] V) : Prop where
  sq_eq_neg : J.comp J = -LinearMap.id

/-- A complex structure $J$ is compatible with a symplectic form $\Omega$ iff $J^2 = -I$,
$\Omega(Ju, Jv) = \Omega(u, v)$ (preservation), and $\Omega(u, Ju) > 0$ for $u \neq 0$ (taming). -/
structure IsCompatibleComplexStr (Ω : LinearMap.BilinForm ℝ V) (J : V →ₗ[ℝ] V) : Prop where
  complex_str : IsComplexStructure J
  preserves : ∀ u v, Ω (J u) (J v) = Ω u v
  positive : ∀ u, u ≠ 0 → Ω u (J u) > 0

end SymplecticLinearAlgebra
