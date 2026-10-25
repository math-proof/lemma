/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareGridConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Calculus.Taylor
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part2


namespace StatMech.Universality

open Set

noncomputable section

def complexAxialFourNeighborStencil
    (f : Complex → Real) (z : Complex) (h : Real) : Real :=
  f (z + (h : Complex)) + f (z - (h : Complex)) +
    f (z + (h : Complex) * Complex.I) +
      f (z - (h : Complex) * Complex.I) - 4 * f z


end
end StatMech.Universality
