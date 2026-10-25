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
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifoldMathlib
set_option autoImplicit false

open scoped TensorProduct


namespace SymplecticGeometry

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The musical isomorphism $\flat : T_xE \to T^*_xE$ at $x$, sending $v$ to
$\omega_x(v, \cdot)$. -/
noncomputable def SymplecticManifold.flat (S : SymplecticManifold n E) (x : E) :
    E →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ) :=
  (S.ω x).curryLeft

end SymplecticGeometry
