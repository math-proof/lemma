/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing.Part3
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
open MeasureTheory Set


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


def tracePullbackPatternSet (S : Finset E) (A : Set (↑S -> Bool)) :
    Set (↑S -> Nat) :=
  {a | (fun e => decide (0 < a e)) ∈ A}

end StatMech.FrontierB
