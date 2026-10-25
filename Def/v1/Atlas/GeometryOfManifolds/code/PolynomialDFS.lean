/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PolynomialDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
set_option autoImplicit false


/-- Polynomial $p$-forms on $\mathbb{R}$: real polynomials in degrees $0$ and $1$, trivial otherwise. -/
@[reducible] def PolyΩ : ℕ → Type
  | 0 => Polynomial ℝ
  | 1 => Polynomial ℝ
  | _ + 2 => PUnit

/-- Polynomial vector fields on $\mathbb{R}$: a single polynomial coefficient $X(t) \partial_t$. -/
@[reducible] def PolyVF : Type := Polynomial ℝ

