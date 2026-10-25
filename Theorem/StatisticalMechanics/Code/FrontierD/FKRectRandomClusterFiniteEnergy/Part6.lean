/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFKG.Part2
import Theorem.StatisticalMechanics.Code.FK.CircuitLowerBound.Part6
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFiniteEnergy.Part5
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

theorem fkRectGraphCriticalOpenMass_map_edgeEquiv
    (R : FKRectTorus) (q : Real) (I : Finset R.EdgeIndex) :
    fkRectGraphCriticalOpenMass R q
        (I.map (fkRectEdgeGraphEquiv R).toEmbedding) =
      fkRectCriticalOpenMass R q I := by
  classical
  unfold fkRectGraphCriticalOpenMass fkRectCriticalOpenMass
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (fkRectConfigurationGraphEquiv R)
  intro omega
  have hpred :
      (∀ a ∈ I, omega a = true) ↔
        ∀ e ∈ I.map (fkRectEdgeGraphEquiv R).toEmbedding,
          fkRectConfigurationGraphEquiv R omega e = true := by
    constructor
    · intro h e he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 he
      simpa using h a ha
    · intro h a ha
      have he : fkRectEdgeGraphEquiv R a ∈
          I.map (fkRectEdgeGraphEquiv R).toEmbedding :=
        Finset.mem_map.2 ⟨a, ha, rfl⟩
      simpa using h (fkRectEdgeGraphEquiv R a) he
  by_cases homega : ∀ a ∈ I, omega a = true
  · rw [if_pos homega, if_pos (hpred.1 homega)]
    exact
      (fkRectGraphCriticalRandomClusterProb_configurationGraphEquiv
        R q omega).symm
  · rw [if_neg homega, if_neg (not_congr hpred |>.1 homega)]


theorem fkRectCritical_cFE_pow_le_openMass
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) :
    FK.cFE (fkRectCriticalP q) q ^ I.card ≤
      fkRectCriticalOpenMass R q I := by
  rw [← fkRectGraphCriticalOpenMass_map_edgeEquiv R q I]
  simpa using fkRectGraphCritical_cFE_pow_le_openMass R hq
    (I.map (fkRectEdgeGraphEquiv R).toEmbedding)

end
end StatMech.FrontierD
