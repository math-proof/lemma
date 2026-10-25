/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentParityDetermination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part7
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

def boolSupport {I : Type*} [Fintype I] [DecidableEq I]
    (b : I → Bool) : Finset I := Finset.univ.filter fun i => b i

def boolAvoid {I : Type*} [Fintype I] [DecidableEq I]
    (T : Finset I) : Set (I → Bool) :=
  {b | Disjoint (boolSupport b) T}

end StatMech.FrontierB
