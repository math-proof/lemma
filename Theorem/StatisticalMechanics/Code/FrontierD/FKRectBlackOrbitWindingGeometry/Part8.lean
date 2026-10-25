/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Instance.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part2


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectBlackOrbitShearSubdivisionWord_cyclicNonUturn
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    onsCyclicDirectionNonUturn
      (fkRectBlackOrbitShearSubdivisionWord R omega d) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  have hn : 0 < (fkRectBlackOrbitList pairing d).length :=
    fkRectBlackOrbitList_length_pos pairing d
  letI : NeZero (fkRectBlackOrbitList pairing d).length := ⟨hn.ne'⟩
  unfold fkRectBlackOrbitShearSubdivisionWord
  apply onsRectangularShearSubdivisionWord_cyclicNonUturn
    R.width R.height R.width_pos R.height_pos
  apply onsCyclicDirectionNonUturn_ofFn
  intro k
  exact fkRectBlackOrbitDirection_nonUturn pairing d k


end
end StatMech.FrontierD
