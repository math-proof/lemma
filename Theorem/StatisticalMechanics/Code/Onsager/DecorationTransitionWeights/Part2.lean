/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWeights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCoefficientAssembly.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights.Part2


namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising


theorem ons_decoratedFullWeight_specialized
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (D : ons_DecoratedEvenSubgraph L) :
    (∏ edge ∈ D.1, ons_decSpecializedWeight weight edge) =
      ∏ edge ∈ ons_originalEdgesOfDecorated L D, weight edge := by
  classical
  rw [← ons_decoratedExternalEdges_image L D]
  rw [Finset.prod_image]
  · rw [← Finset.prod_filter_mul_prod_filter_not
      (s := D.1) (p := ons_decIsExternal)]
    simp only [ons_decoratedExternalEdges]
    have hnonext :
        (∏ edge ∈ D.1.filter (fun edge ↦ ¬ ons_decIsExternal edge),
          ons_decSpecializedWeight weight edge) = 1 := by
      apply Finset.prod_eq_one
      intro edge hedge
      have hnot := (Finset.mem_filter.mp hedge).2
      simp [ons_decSpecializedWeight, hnot]
    rw [hnonext, mul_one]
    apply Finset.prod_congr rfl
    intro edge hedge
    have hext := (Finset.mem_filter.mp hedge).2
    simp [ons_decSpecializedWeight, hext]
  · intro edge hedge edge' hedge' hproj
    exact ons_decEdgeProjection_injective_of_external L
      (Finset.mem_filter.mp hedge).2
      (Finset.mem_filter.mp hedge').2 hproj

theorem ons_decoratedFullWeightedSpinSum_specialized
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (a b : Fin 2) :
    ons_decoratedFullWeightedSpinSum L
        (ons_decSpecializedWeight weight) a b =
      ons_weightedSpinCharacterSum L weight a b := by
  rw [ons_weightedSpinCharacterSum_eq_decorated]
  unfold ons_decoratedFullWeightedSpinSum
    ons_decoratedWeightedSpinWeight
  apply Finset.sum_congr rfl
  intro D hD
  rw [ons_decoratedFullWeight_specialized]

end StatMech.Onsager
