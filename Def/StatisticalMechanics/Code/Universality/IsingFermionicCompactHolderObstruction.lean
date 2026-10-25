/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCompactHolderObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part5


namespace StatMech.Universality

open Filter Metric Set Topology

noncomputable section

def meshScaleLinearField (k : Nat) (z : Complex) : Complex :=
  (Real.sqrt (k + 1 : Real) : Complex) * z


end
end StatMech.Universality
