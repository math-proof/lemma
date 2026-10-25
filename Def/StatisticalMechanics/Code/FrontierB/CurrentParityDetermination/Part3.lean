/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityDetermination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part2
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

def currentLocalParity {I : Type*} (a : I → ℕ) : I → Bool :=
  fun i => decide (Odd (a i))

end StatMech.FrontierB
