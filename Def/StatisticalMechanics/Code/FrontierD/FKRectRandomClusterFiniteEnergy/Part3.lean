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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFiniteEnergy.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

noncomputable def fkRectGraphCriticalOpenMass
    (R : FKRectTorus) (q : Real)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) : Real :=
  ∑ eta ∈ Finset.univ.filter
      (fun eta : FKRectGraphConfiguration R => ∀ e ∈ I, eta e = true),
    fkRectGraphCriticalRandomClusterProb R q eta

def fkRectGraphOpenIndicator
    (R : FKRectTorus)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) : Real :=
  if ∀ e ∈ I, eta e = true then 1 else 0

end
end StatMech.FrontierD
