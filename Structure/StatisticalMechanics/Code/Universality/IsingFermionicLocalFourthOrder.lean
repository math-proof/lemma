/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalFourthOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalFourthOrder


namespace StatMech.Universality

open Set

noncomputable section

structure CenteredFourthOrderSegmentData
    (g : Real -> Real) (h M : Real) : Prop where
  atZero : ContDiffAt Real 4 g 0
  positive : ContDiffOn Real 4 g (uIcc 0 h)
  negative : ContDiffOn Real 4 g (uIcc 0 (-h))
  fourthPositive : forall t, t ∈ uIcc 0 h ->
    |iteratedDeriv 4 g t| <= M
  fourthNegative : forall t, t ∈ uIcc 0 (-h) ->
    |iteratedDeriv 4 g t| <= M


end
end StatMech.Universality
