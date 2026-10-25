/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/HierarchyTheorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Structure.v1.Atlas.TheoryOfComputation.code.HierarchyTheorems.Part2


namespace HierarchyTheorems

open TuringMachine

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/--
One computation step of a deterministic oracle TM. If the current state is
`qAccept` or `qReject`, the configuration is left unchanged (halted). Otherwise
the oracle answer is computed (as `queryTape ∈ oracle` when in `qQuery`, else
`false`), `δ` is consulted, and the head, state, and tape are updated.
-/
noncomputable def OracleTM.step (M : OracleTM Q Γ) (c : OracleConfig Q Γ) :
    OracleConfig Q Γ :=
  if c.state = M.qAccept ∨ c.state = M.qReject then c
  else
    let oracleAnswer : Bool :=
      if c.state = M.qQuery then
        Classical.propDecidable (c.queryTape ∈ M.oracle) |>.decide
      else false
    let (q', b, d) := M.δ c.state (c.tape c.headPos) oracleAnswer
    { state := q'
      headPos := match d with
        | Direction.L => c.headPos - 1
        | Direction.R => c.headPos + 1
      tape := Function.update c.tape c.headPos b
      queryTape := c.queryTape }

/-- `M.run c n` applies `M.step` exactly `n` times starting from configuration `c`. -/
noncomputable def OracleTM.run (M : OracleTM Q Γ) (c : OracleConfig Q Γ) :
    ℕ → OracleConfig Q Γ
  | 0 => c
  | n + 1 => M.step (M.run c n)

/--
The initial oracle TM configuration on input `w`: state is `q₀`, head at position
`0`, tape contains `w` on cells `0, …, w.length - 1` and `blank` elsewhere, and the
query tape is empty.
-/
def OracleTM.initConfig (M : OracleTM Q Γ) (w : List Γ) : OracleConfig Q Γ where
  state := M.q₀
  headPos := 0
  tape := fun i =>
    if h : 0 ≤ i ∧ i < w.length then
      w.get ⟨i.toNat, by omega⟩
    else M.blank
  queryTape := []

/-- Run `M` for `n` steps starting from its initial configuration on input `w`. -/
noncomputable def OracleTM.runOnInput (M : OracleTM Q Γ) (w : List Γ) (n : ℕ) :
    OracleConfig Q Γ :=
  M.run (M.initConfig w) n

/-- `M.accepts w` if some finite-step run of `M` on input `w` ends in `qAccept`. -/
noncomputable def OracleTM.accepts (M : OracleTM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ, (M.runOnInput w n).state = M.qAccept

/-- `M.halts w` if some finite-step run of `M` on `w` reaches `qAccept` or `qReject`. -/
noncomputable def OracleTM.halts (M : OracleTM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ, (M.runOnInput w n).state = M.qAccept ∨
            (M.runOnInput w n).state = M.qReject

/-- The **language** of an oracle TM `M` is the set of strings it accepts. -/
noncomputable def OracleTM.language (M : OracleTM Q Γ) : Set (List Γ) :=
  {w | M.accepts w}

/-- An oracle TM `M` is a **decider** if it halts on every input. -/
noncomputable def OracleTM.isDecider (M : OracleTM Q Γ) : Prop :=
  ∀ w : List Γ, M.halts w

/-- `M.decides B` means `M` is a decider and `L(M) = B`. -/
noncomputable def OracleTM.decides (M : OracleTM Q Γ) (B : Set (List Γ)) : Prop :=
  M.isDecider ∧ M.language = B

/--
`M.runsInTime t` if on every input `w`, `M` reaches an accept or reject state
within `t(|w|)` steps.
-/
noncomputable def OracleTM.runsInTime (M : OracleTM Q Γ) (t : ℕ → ℕ) : Prop :=
  ∀ w : List Γ,
    (M.runOnInput w (t w.length)).state = M.qAccept ∨
    (M.runOnInput w (t w.length)).state = M.qReject

end HierarchyTheorems
