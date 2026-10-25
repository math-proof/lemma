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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec24RiemannRochSerre
set_option maxHeartbeats 800000


noncomputable section

namespace Lec24

/-- Axiomatic data for a locally free sheaf on `ℙ¹_k`: its rank and degree together with
the cohomology dimensions of its Serre twists, satisfying the expected Euler-characteristic
formula. -/
structure LocallyFreeSheafOnP1 where
  rank : ℕ
  degree : ℤ
  h0_twist : ℤ → ℕ
  h1_twist : ℤ → ℕ
  euler_char_twist : ∀ d : ℤ,
    (h0_twist d : ℤ) - (h1_twist d : ℤ) = degree + rank * d + rank

end Lec24
end
