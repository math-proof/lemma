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
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec24RiemannRochSerre
set_option maxHeartbeats 800000


noncomputable section

namespace Lec24

/-- The split bundle `⨁ᵢ O_{ℙ¹}(dᵢ)` on `ℙ¹`, packaged as a `LocallyFreeSheafOnP1`. -/
def splitBundle (n : ℕ) (degrees : Fin n → ℤ) : LocallyFreeSheafOnP1 where
  rank := n
  degree := ∑ i, degrees i
  h0_twist := fun d => ∑ i : Fin n, h0_P1 (degrees i + d)
  h1_twist := fun d => ∑ i : Fin n, h1_P1 (degrees i + d)
  euler_char_twist := by
    intro d
    push_cast
    have key : ∀ i : Fin n,
        (h0_P1 (degrees i + d) : ℤ) - (h1_P1 (degrees i + d) : ℤ) = degrees i + d + 1 :=
      fun i => euler_char_O_d_P1 (degrees i + d)
    rw [← Finset.sum_sub_distrib]
    simp_rw [key]
    simp [Finset.sum_add_distrib]

end Lec24
end
