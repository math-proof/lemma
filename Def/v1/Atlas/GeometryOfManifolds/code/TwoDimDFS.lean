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
import Abbrev.v1.Atlas.GeometryOfManifolds.code.TwoDimDFS
set_option autoImplicit false
set_option maxHeartbeats 800000


noncomputable section

/-- Polynomial $p$-forms on $\mathbb{R}^2$: scalars for $p = 0, 2$, pairs of polynomials for
$p = 1$ (the components of $f\, dx + g\, dy$), and trivial in degrees $\ge 3$. -/
@[reducible] def Symp2Ω : ℕ → Type
  | 0 => Poly2
  | 1 => Poly2 × Poly2
  | 2 => Poly2
  | _ + 3 => PUnit

/-- Polynomial vector fields on $\mathbb{R}^2$: pairs $(a, b)$ representing
$a\, \partial_x + b\, \partial_y$. -/
@[reducible] def Symp2VF : Type := Poly2 × Poly2


end
