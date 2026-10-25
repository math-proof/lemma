/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP3Domain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]


def shb_P3DomainResummation
    (H G : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (β : ℝ) (J : Sym2 V → ℝ) {x y : V}
    (p : H.Path x y) : Prop :=
  shb_backboneNumSupport G β J x y (shb_pathMapLe hHG p) *
      currentSum H β J ∅ ≤
    shb_backboneNumSupport H β J x y p * currentSum G β J ∅


end StatMech.Sharpness
