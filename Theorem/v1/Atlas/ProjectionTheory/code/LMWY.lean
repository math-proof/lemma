/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LMWY.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.LMWY
open Matrix


namespace HomogeneousDynamics

/-- The unipotent matrix $U(t)$ has determinant $1$. -/
lemma unipotentU_det (t : ℝ) : (unipotentU t).det = 1 := by
  simp [unipotentU, Matrix.det_fin_three]

end HomogeneousDynamics
