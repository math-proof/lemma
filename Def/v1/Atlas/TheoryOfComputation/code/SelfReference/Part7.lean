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
import Structure.v1.Atlas.TheoryOfComputation.code.SelfReference.Part6


namespace TuringMachine

open TuringMachine

/-- A `FormalProofSystem` is *complete* if every true non-acceptance statement
is provable: whenever `d` does not accept, `⟨d⟩ ∈ provable`. Gödel's
First Incompleteness Theorem says no sound, recognizable system can be complete
in this sense. -/
def FormalProofSystem.isComplete {Γ : Type} (F : FormalProofSystem Γ) : Prop :=
  ∀ (d : TMDesc Γ), ¬d.accepts → F.enc.encode d ∈ F.provable

end TuringMachine
