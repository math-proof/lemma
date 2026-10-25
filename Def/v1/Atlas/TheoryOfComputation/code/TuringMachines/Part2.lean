/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.RelClasses
import Structure.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part3


namespace TuringMachine

open Direction

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/-- An LBA `B` accepts `w` iff its underlying TM accepts `w`. -/
def LBA.accepts (B : LBA Q Γ) (w : List Γ) : Prop :=
  B.toTM.accepts w

/-- The language recognized by an LBA, inherited from its underlying TM. -/
def LBA.language (B : LBA Q Γ) : Set (List Γ) :=
  B.toTM.language

/-- An LBA is a decider iff its underlying TM halts on every input. -/
def LBA.isDecider (B : LBA Q Γ) : Prop :=
  B.toTM.isDecider

end TuringMachine
