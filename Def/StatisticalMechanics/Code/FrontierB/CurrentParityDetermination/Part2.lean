/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityDetermination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

def boolLower {I : Type*} [Fintype I] [DecidableEq I]
    (b : I → Bool) : Finset (I → Bool) :=
  Finset.univ.filter fun a => boolSupport a ⊂ boolSupport b

end StatMech.FrontierB
