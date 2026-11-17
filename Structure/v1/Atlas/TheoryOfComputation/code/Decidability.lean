/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Decidability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Countable
public import Mathlib.Computability.Language
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
public import Notation.v1.Atlas.TheoryOfComputation.code.Reductions
public import Def.v1.Atlas.TheoryOfComputation.code.Decidability


public section

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
