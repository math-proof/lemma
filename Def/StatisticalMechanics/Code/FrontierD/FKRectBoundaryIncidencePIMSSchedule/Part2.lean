/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceScheduledCapstone
import Mathlib.Data.Nat.Choose.Bounds
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

noncomputable section

def fkRectPIMSSublinearThreshold (depth height : Nat) : Nat :=
  if depth = 0 then height else height / depth


end
end StatMech.FrontierD
