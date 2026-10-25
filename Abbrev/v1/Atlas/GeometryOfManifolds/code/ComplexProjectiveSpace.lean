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
import Instance.v1.Atlas.GeometryOfManifolds.code.ComplexProjectiveSpace
set_option autoImplicit false

open scoped Manifold ContDiff


noncomputable section

/-- The smooth atlas on $\mathbb{CP}^n$ making it a $(2n)$-dimensional real charted space (via affine charts $U_i = \{[z_0 : \cdots : z_n] : z_i \ne 0\}$). -/
abbrev CPn_Ω (n : ℕ) : ℕ → Type :=
  ManifoldΩ (𝓡 (2 * n)) (ComplexProjectiveSpace n)

/-- Vector fields $\mathfrak{X}(\mathbb{CP}^n)$ in the DFS framework. -/
abbrev CPn_VF (n : ℕ) : Type :=
  ManifoldVF (𝓡 (2 * n)) (ComplexProjectiveSpace n)

end
