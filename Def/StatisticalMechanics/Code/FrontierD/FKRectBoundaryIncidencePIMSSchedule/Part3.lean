/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceScheduledCapstone
import Mathlib.Data.Nat.Choose.Bounds
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule.Part2
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectPIMSHeightLower
    (c : Real) (width : Nat) : Nat :=
  max width (Nat.find (exists_fkRectPIMSHeightDominating c width))

end
end StatMech.FrontierD
