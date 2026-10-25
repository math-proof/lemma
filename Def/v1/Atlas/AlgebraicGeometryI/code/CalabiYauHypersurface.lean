/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Structure.v1.Atlas.AlgebraicGeometryI.code.CalabiYauHypersurface
set_option maxHeartbeats 400000


namespace CYHyp

/-- Build a `SmoothCompleteCurve'` of genus `g` with canonical degree `2g - 2`. -/
def mkCurve' (g : ℕ) : SmoothCompleteCurve' where
  g := g
  degK := 2 * (g : ℤ) - 2

/-- Arithmetic genus of a smooth plane curve of degree `d`: `(d-1)(d-2)/2`. -/
def genus_plane_curve (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

end CYHyp
