/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/MoserCorrectness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic
public import Abbrev.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.MoserCorrectness

@[expose] public section

set_option maxHeartbeats 400000

open Finset


namespace MoserCorrectness

/-- The clause $C$ is satisfied by the assignment $\sigma$ if at least one of its literals evaluates to `true`. -/
def Clause.satisfied (C : Clause n k) (σ : Assignment n) : Prop :=
  ∃ i : Fin k, (C.lits i).polarity = σ (C.lits i).var

end MoserCorrectness
