/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareGridConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Analysis.Calculus.Taylor
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency

@[expose] public section

namespace StatMech.Universality

open Set

noncomputable section

def directionalFourNeighborStencil
    (g₁ g₂ : Real → Real) (h : Real) : Real :=
  (g₁ h + g₁ (-h) - 2 * g₁ 0) +
    (g₂ h + g₂ (-h) - 2 * g₂ 0)


end
end StatMech.Universality
