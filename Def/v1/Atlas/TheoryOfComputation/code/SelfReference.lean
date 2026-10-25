/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part13
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Decidability
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Set
import Structure.v1.Atlas.TheoryOfComputation.code.SelfReference


namespace SelfReference

open TuringMachine

/-- The language `L(d)` recognized by the Turing machine packaged inside `d`. -/
def TMDescription.lang {Γ : Type} (d : TMDescription Γ) : Set (List Γ) :=
  @TM.language d.Q Γ d.decEq d.machine

variable {Γ : Type}

/-- `M.haltsWithOutput w out` says that running `M.machine` on input `w` reaches a
halt configuration after some number of steps `n`, and at that point the first
`out.length` cells of the tape spell out `out`. This is the "halt with `out` on the
tape" predicate used to formalize the printing/output behavior of TMs. -/
def TMDescription.haltsWithOutput (M : TMDescription Γ) (w out : List Γ) : Prop :=
  letI := M.decEq
  ∃ n : ℕ,
    M.machine.isHaltConfig (M.machine.runOnInput w n) ∧
    Config.readTape (M.machine.runOnInput w n) out.length = out

end SelfReference
