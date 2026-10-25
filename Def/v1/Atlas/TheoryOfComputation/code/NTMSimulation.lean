/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NTMSimulation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
open TuringMachine SpaceComplexity Direction


namespace TuringMachine

/-- Simulate the NTM `M` on input `w` along a fixed nondeterministic-choice
sequence `choices : ℕ → Q × Γ × Direction`. At step `n`:
- if the current configuration is halting, stay put;
- if `choices n` is a valid transition from the current configuration, apply it;
- otherwise, stay put (the chosen transition is illegal here). -/
noncomputable def NTM.runWithChoices {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]
    (M : NTM Q Γ) (w : List Γ) (choices : ℕ → Q × Γ × Direction) :
    ℕ → Config Q Γ
  | 0 => M.initConfig w
  | n + 1 =>
    let c := M.runWithChoices w choices n
    if c.state = M.qAccept ∨ c.state = M.qReject then c
    else
      have : Decidable (choices n ∈ M.δ c.state (c.tape c.headPos)) :=
        Classical.dec _
      if choices n ∈ M.δ c.state (c.tape c.headPos) then
        M.stepWith c (choices n)
      else c

end TuringMachine
