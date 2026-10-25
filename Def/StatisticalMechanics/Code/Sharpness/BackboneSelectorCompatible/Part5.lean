/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2Quantitative
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part4
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]


def shb_P2ComplementResummation
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {x z u : V}
    (p₁₂ : G.Path x z) (p₁ : G.Path x u) (p₂ : H.Path u z) : Prop :=
  shb_backboneNumSupport G β J x z p₁₂ * currentSum H β J ∅ =
    shb_backboneNumSupport G β J x u p₁ *
      shb_backboneNumSupport H β J u z p₂


end StatMech.Sharpness
