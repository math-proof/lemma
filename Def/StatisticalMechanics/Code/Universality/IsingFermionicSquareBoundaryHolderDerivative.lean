/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryCompactAverage.Part2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Hull
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryHolderDerivative


namespace StatMech.Universality

open Set Metric

noncomputable section

def lagrangeShrinkingTwoPointPosition (k : Nat) : Fin 2 → Complex :=
  ![0, ((k + 1 : Nat) : Complex)⁻¹]


def lagrangeShrinkingTwoPointValue : Fin 2 → Complex := ![0, 1]

end
end StatMech.Universality
