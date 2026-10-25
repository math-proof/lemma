/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Archimedean.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.SubdivisionSmall


noncomputable section

namespace AlgebraicTopologyI

variable {X : Type*} [TopologicalSpace X]

/-- The barycentric subdivision vertex coordinates are nonnegative. -/
lemma barySubdivVertex_nonneg (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k i : Fin (n + 1)) : 0 ≤ barySubdivVertex n π k i := by
  simp only [barySubdivVertex]; split <;> positivity

/-- The barycentric coordinates of any vertex of the barycentric subdivision sum to one,
exhibiting it as a point of the standard simplex. -/
lemma barySubdivVertex_sum (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    ∑ i : Fin (n + 1), barySubdivVertex n π k i = 1 := by
  simp only [barySubdivVertex]
  rw [← Finset.sum_filter]
  have hfilt : (Finset.univ.filter (fun i => ∃ j : Fin (n + 1), j ≤ k ∧ π j = i)) =
    (Finset.Iic k).image π := by
    ext i; simp [Finset.mem_filter, Finset.mem_image, Finset.mem_Iic]
  rw [hfilt, Finset.sum_const, Finset.card_image_of_injective _ π.injective, Fin.card_Iic]
  simp only [nsmul_eq_mul]
  push_cast
  field_simp

/-- The barycentric subdivision map sends a point of the standard simplex to a point of
the standard simplex. -/
lemma barySubdivMapFn_mem (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (t : Fin (n + 1) → ℝ) (ht : t ∈ stdSimplex ℝ (Fin (n + 1))) :
    barySubdivMapFn n π t ∈ stdSimplex ℝ (Fin (n + 1)) := by
  constructor
  · intro i
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (ht.1 k) (barySubdivVertex_nonneg n π k i)
  · simp only [barySubdivMapFn]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, barySubdivVertex_sum, mul_one]
    exact ht.2

/-- The barycentric subdivision map is continuous, as a self-map of the standard simplex. -/
lemma barySubdivMap_continuous (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    Continuous (fun (t : ↥(stdSimplex ℝ (Fin (n + 1)))) =>
      (⟨barySubdivMapFn n π t.1, barySubdivMapFn_mem n π t.1 t.2⟩ :
        ↥(stdSimplex ℝ (Fin (n + 1))))) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  simp only [barySubdivMapFn]
  apply continuous_finset_sum
  intro k _
  exact ((continuous_apply k).comp continuous_subtype_val).mul continuous_const

end AlgebraicTopologyI
end
