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
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFiniteEnergy
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

theorem fkRectGraphCriticalClosedMass_empty
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    fkRectGraphCriticalClosedMass R q ∅ = 1 := by
  classical
  unfold fkRectGraphCriticalClosedMass
  rw [show Finset.univ.filter
      (fun eta : FKRectGraphConfiguration R =>
        ∀ e ∈ (∅ : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}),
          eta e = false) = Finset.univ by ext eta; simp]
  exact sum_fkRectGraphCriticalRandomClusterProb R hq


end
end StatMech.FrontierD
