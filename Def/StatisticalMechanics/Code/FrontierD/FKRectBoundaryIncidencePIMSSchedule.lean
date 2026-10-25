/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceScheduledCapstone
import Mathlib.Data.Nat.Choose.Bounds
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

noncomputable section

def fkRectPIMSDecayDepth (a : Real) (p : Nat → Real) (k : Nat) : Nat :=
  Nat.findGreatest (fun d => p k ≤ a ^ d) k


end
end StatMech.FrontierD
