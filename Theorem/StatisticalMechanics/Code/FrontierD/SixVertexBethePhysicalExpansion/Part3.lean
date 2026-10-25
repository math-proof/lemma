/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sum_powerset_neg_one (s : Finset (Fin (n + 1))) :
    (∑ t ∈ s.powerset, (-1 : Complex) ^ t.card) =
      if s = ∅ then 1 else 0 := by
  calc
    (∑ t ∈ s.powerset, (-1 : Complex) ^ t.card) =
        ∑ t ∈ s.powerset, ∏ _i ∈ t, (-1 : Complex) := by simp
    _ = ∏ _i ∈ s, (1 + (-1 : Complex)) :=
      (Finset.prod_one_add s).symm
    _ = if s = ∅ then 1 else 0 := by
      by_cases hs : s = ∅
      · simp [hs]
      · rw [if_neg hs]
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        exact Finset.prod_eq_zero hi (by ring)


theorem sixVertexBetheCollisionFreeIntervalSum_inclusionExclusion
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) :
    sixVertexBetheCollisionFreeIntervalSum N c z x =
      ∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
        (-1 : Complex) ^ S.card *
          sixVertexBetheCollisionConstrainedIntervalSum N c z x S := by
  classical
  unfold sixVertexBetheCollisionFreeIntervalSum
    sixVertexBetheCollisionConstrainedIntervalSum
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_filter]
  have hfilter :
      ((Finset.univ : Finset (Fin (n + 1))).powerset.filter
          (fun S => S ⊆ sixVertexBetheCollisionSet N x q)) =
        (sixVertexBetheCollisionSet N x q).powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ,
      true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨Finset.Subset.trans h (Finset.subset_univ _), h⟩
  rw [hfilter, ← Finset.sum_mul, sum_powerset_neg_one]
  by_cases hfree : sixVertexBetheCollisionSet N x q = ∅ <;>
    simp [hfree]


end
end StatMech.FrontierD
