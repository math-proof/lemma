/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionSymmetry
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4RadialDecay.Part3
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

theorem fkQgt4SiteSphere_card_le (n : Nat) :
    (fkQgt4SiteSphere n).card <= (2 * n + 1) ^ 2 := by
  calc
    (fkQgt4SiteSphere n).card <= (box_finite 2 n).toFinset.card :=
      Finset.card_filter_le _ _
    _ = (2 * n + 1) ^ 2 := by
      rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]


end
end StatMech.FrontierD
