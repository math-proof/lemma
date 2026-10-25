/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Mathlib.Algebra.Order.Chebyshev
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

noncomputable def constantRadialTensorTent (k : Nat) : Complex → Complex :=
  finiteRadialGridInterpolant (k + 2) (1 / (k + 2 : Real)) (fun _ _ ↦ 1)


def constantRadialTensorTentBoundaryPoint (k : Nat) : Complex :=
  isingRadialGridPosition (1 / (k + 2 : Real)) 0 0


def constantRadialTensorTentExteriorPoint (k : Nat) : Complex :=
  isingRadialGridCellPoint (1 / (k + 2 : Real)) 0 0 (-1) 0

end
end StatMech.Universality
