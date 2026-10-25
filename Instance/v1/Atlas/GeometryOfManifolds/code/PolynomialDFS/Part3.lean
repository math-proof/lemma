/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PolynomialDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Theorem.v1.Atlas.GeometryOfManifolds.code.PolynomialDFS.Part2
set_option autoImplicit false


/-- Nontriviality instance for polynomial $0$-forms. -/
instance : Nontrivial (PolyΩ 0) := ⟨⟨0, 1, polyOmega_zero_nontrivial⟩⟩

/-- Nontriviality instance for polynomial $1$-forms. -/
instance : Nontrivial (PolyΩ 1) := ⟨⟨0, 1, polyOmega_one_nontrivial⟩⟩

