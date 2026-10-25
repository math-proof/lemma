/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareGridConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Calculus.Taylor
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part3


namespace StatMech.Universality

open Set

noncomputable section

def complexDirectionalFourNeighborStencil
    (f : Complex → Real) (z v₁ v₂ : Complex) (h : Real) : Real :=
  f (z + (h : Complex) * v₁) + f (z - (h : Complex) * v₁) +
    f (z + (h : Complex) * v₂) + f (z - (h : Complex) * v₂) - 4 * f z


end
end StatMech.Universality
