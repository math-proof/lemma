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
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4RadialDecay.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

def fkQgt4SiteRadius (x : Site 2) : Nat :=
  (x 0).natAbs + (x 1).natAbs


def fkQgt4SiteSphere (n : Nat) : Finset (Site 2) :=
  (box_finite 2 n).toFinset.filter (fun x => fkQgt4SiteRadius x = n)

end
end StatMech.FrontierD
