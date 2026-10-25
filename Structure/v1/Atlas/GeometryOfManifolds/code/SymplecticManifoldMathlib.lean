/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticManifoldMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Dimension.Finrank
import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticManifoldMathlib
set_option autoImplicit false

open scoped TensorProduct


namespace SymplecticGeometry

/-- A symplectic manifold of dimension $2n$: a $2$-form $\omega$ on $E$ that is closed
($d\omega = 0$) and nondegenerate (the top wedge $\omega^n$ is a volume form). -/
structure SymplecticManifold (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  ω : E → (E [⋀^Fin 2]→L[ℝ] ℝ)
  dim_eq : Module.finrank ℝ E = 2 * n
  closed : ∀ x : E, extDeriv ω x = 0
  nondegenerate : ∀ x : E, AlternatingMap.wedgePower ((ω x).toAlternatingMap) n ≠ 0


end SymplecticGeometry
