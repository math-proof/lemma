/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

def hexCSExteriorTailTurn {T L : ℕ} (e : HexCSIncidence T L) : ℤ :=
  match e.vtx.1.color, e.edge with
  | .black, 0 => if 0 ≤ hexAWTrans e.vtx.1 then 2 else -2
  | .white, 0 => 0
  | .white, 1 => 2
  | .white, 2 => -1
  | _, _ => 0

end
end StatMech.Universality
