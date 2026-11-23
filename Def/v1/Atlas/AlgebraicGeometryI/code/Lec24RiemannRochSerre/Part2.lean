/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Structure.v1.Atlas.AlgebraicGeometryI.code.SerreDualityStatement
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityStatement
public import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec24RiemannRochSerre

@[expose] public section

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
