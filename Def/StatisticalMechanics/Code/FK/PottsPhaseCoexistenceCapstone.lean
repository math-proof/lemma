/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsPhaseCoexistenceCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolumePhaseTransport.Part2
open Filter MeasureTheory Topology


namespace StatMech.FK

noncomputable section

def pottsSelfDualInverseTemperature (q : Nat) (J : Real) : Real :=
  Real.log (1 + Real.sqrt q) / J

end
end StatMech.FK
