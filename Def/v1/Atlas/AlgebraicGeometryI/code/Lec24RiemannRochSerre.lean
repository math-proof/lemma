/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Int.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Structure.v1.Atlas.AlgebraicGeometryI.code.SerreDualityStatement
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityStatement
set_option maxHeartbeats 800000


noncomputable section

namespace Lec24

/-- The dimension `h⁰(ℙ¹, O(d)) = max(d + 1, 0)`. -/
def h0_P1 (d : ℤ) : ℕ := (d + 1).toNat

/-- The dimension `h¹(ℙ¹, O(d)) = max(-d - 1, 0)`, dual to `h⁰(ℙ¹, O(-d - 2))`. -/
def h1_P1 (d : ℤ) : ℕ := (-d - 1).toNat

end Lec24
end
