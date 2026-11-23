/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SelfReference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
public import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part13
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Decidability
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Set
public import Structure.v1.Atlas.TheoryOfComputation.code.SelfReference.Part5

@[expose] public section

namespace TuringMachine

open TuringMachine

/-- The complement `\overline{A_{TM}}` of the acceptance language `A_TM`. This
language is famously *not* Turing-recognizable and is the one whose
"unprovability" gives Gödel-style results in this development. -/
def A_TM_complement (enc : TMEncoding Γ) : Set (List Γ) :=
  (A_TM enc)ᶜ

end TuringMachine
