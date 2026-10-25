/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ComplexProjectiveSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ManifoldDFS
import Def.v1.Atlas.GeometryOfManifolds.code.ManifoldDFS.Part2
import Def.v1.Atlas.GeometryOfManifolds.code.ComplexProjectiveSpace
set_option autoImplicit false

open scoped Manifold ContDiff


noncomputable section

/-- $\mathbb{CP}^n$ carries the quotient topology from $\mathbb{C}^{n+1} \setminus \{0\}$. -/
instance CPn_topologicalSpace (n : ℕ) : TopologicalSpace (ComplexProjectiveSpace n) :=
  instTopologicalSpaceQuotient (s := CPnSetoid n)


end
