/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCoefficientAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientInduction.Part2
import Def.StatisticalMechanics.Code.Onsager.DecorationCoefficientAssembly


namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising


theorem ons_weightedSpinEdgeCoefficient_eq_decoratedCycleSplit
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) (d : ons_Dart L) :
    ons_weightedSpinEdgeCoefficient L weight a b (ons_portEdge L d) =
      ∑ D : ons_DecoratedContainingEdge L d,
        -ons_edgeWeight
            (ons_KWmatWeightedPhase L weight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))
            (ons_decCycleFirstReturn
              (ons_decoratedEdgeSplit L d D).cycle) *
          ons_decoratedWeightedSpinWeight L weight a b
            (ons_decoratedEdgeSplit L d D).remainder := by
  classical
  rw [ons_weightedSpinEdgeCoefficient_eq_decorated]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype
    (p := fun D : ons_DecoratedEvenSubgraph L ↦
      s(d, ons_dartRev L d) ∈ D.1)
    (Finset.univ.filter
      (fun D : ons_DecoratedEvenSubgraph L ↦
        s(d, ons_dartRev L d) ∈ D.1)) (by simp)]
  apply Finset.sum_congr rfl
  intro D hD
  let S := ons_decoratedEdgeSplit L d D
  have hisotropic :=
    ons_decCycle_remainder_originalHomology_isotropic
      L S.cycle S.cycle_isCycle S.remainder S.remainder_zero
  have hfactor := ons_decoratedWeightedSpinWeight_split_of_isotropic
    L D.1 S.remainder S.cycle S.edge_split S.edge_disjoint
      weight a b hisotropic
  have hcycle := ons_decCycleFirstReturn_weight_eq_neg_spinCharacter
    S.cycle S.cycle_isCycle S.cycle_snd weight a b
  rw [hfactor, hcycle]
  ring


end StatMech.Onsager
