/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDimensionCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.ChevalleyImage
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ChevalleyImage
import Def.v1.Atlas.AlgebraicGeometryI.code.BertiniDimensionCount.Part2


namespace BertiniArithmetic

/-- Bertini's theorem (abstract): for any smooth subvariety `X ⊆ ℙⁿ`, there exists a hyperplane
giving a smooth section (Thm 22.1, Lec 22). -/
structure BertiniThm221 (X : SmoothSubvariety) where
  incidence_dim : X.d + (X.n - X.d - 1) = X.n - 1
  incidence_lt_dual : X.n - 1 < X.n
  smooth_section_exists : ∃ H : X.HyperplaneIndex, X.isSmoothSection H

end BertiniArithmetic
