/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PolynomialDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Instance.v1.Atlas.GeometryOfManifolds.code.PolynomialDFS.Part2
set_option autoImplicit false


/-- The space of polynomial $0$-forms is nontrivial: $0 \ne 1$. -/
theorem polyOmega_zero_nontrivial : (0 : PolyΩ 0) ≠ (1 : PolyΩ 0) :=
  one_ne_zero.symm

/-- The space of polynomial $1$-forms is nontrivial: $0 \ne 1$. -/
theorem polyOmega_one_nontrivial : (0 : PolyΩ 1) ≠ (1 : PolyΩ 1) :=
  one_ne_zero.symm

