/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Countable
import Mathlib.Computability.Language
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
import Def.v1.Atlas.TheoryOfComputation.code.Decidability


namespace Decidability

/-- A `TMDesc` packages a Turing machine together with its (decidable) state type and an input
string. This corresponds to the encoded pair `⟨M, w⟩` used throughout Sipser's undecidability
arguments — for example, the input to a putative decider for `A_TM`. -/
structure TuringMachine.TMDesc (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  tm : TuringMachine.TM Q Γ
  input : List Γ

end Decidability
