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
import Structure.v1.Atlas.TheoryOfComputation.code.SelfReference.Part5


namespace TuringMachine

open TuringMachine

/-- The complement `\overline{A_{TM}}` of the acceptance language `A_TM`. This
language is famously *not* Turing-recognizable and is the one whose
"unprovability" gives Gödel-style results in this development. -/
def A_TM_complement (enc : TMEncoding Γ) : Set (List Γ) :=
  (A_TM enc)ᶜ

end TuringMachine
