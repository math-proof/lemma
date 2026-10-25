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
import Abbrev.v1.Atlas.GeometryOfManifolds.code.ComplexProjectiveSpace
set_option autoImplicit false

open scoped Manifold ContDiff


noncomputable section

/-- The differential-form-space structure on $\mathbb{CP}^n$. -/
noncomputable instance instCPnDFS (n : ℕ) :
    DifferentialFormSpace (CPn_Ω n) (CPn_VF n) :=
  manifoldDFS (𝓡 (2 * n)) (ComplexProjectiveSpace n)


end
