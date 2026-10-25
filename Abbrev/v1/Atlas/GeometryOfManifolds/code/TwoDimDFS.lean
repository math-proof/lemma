/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/TwoDimDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
set_option autoImplicit false
set_option maxHeartbeats 800000


noncomputable section

/-- Real polynomials in two variables $\mathbb{R}[x_0, x_1]$, used as the function ring
underlying the polynomial DFS on $\mathbb{R}^2$. -/
abbrev Poly2 := MvPolynomial (Fin 2) ℝ

end
