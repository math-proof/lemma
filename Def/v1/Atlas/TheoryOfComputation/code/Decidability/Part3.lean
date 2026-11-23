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
public import Structure.v1.Atlas.TheoryOfComputation.code.Decidability.Part2

@[expose] public section

namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace TuringMachine

variable {Γ : Type}

/-- The acceptance problem for Turing machines: `A_TM = {⟨M, w⟩ | M accepts w}`.
The classical Sipser theorem says this language is undecidable but Turing-recognizable. -/
def A_TM (enc : TMEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : TMDesc Γ, enc.encode d = s ∧ d.accepts}

/-- The halting problem: `HALT_TM = {⟨M, w⟩ | M halts on w}`, also undecidable. -/
def HALT_TM (enc : TMEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : TMDesc Γ, enc.encode d = s ∧ d.halts}

/-- The "flipped" TM `H.flip` swaps the accept and reject states of `H`. If `H` is a decider
then `H.flip` decides the complement of `L(H)`. This is the standard construction used in the
diagonal proof that `A_TM` is undecidable. -/
def TuringMachine.TM.flip {Q : Type} (Γ : Type) [DecidableEq Q] (H : TuringMachine.TM Q Γ) :
    TuringMachine.TM Q Γ where
  blank := H.blank
  inputAlpha := H.inputAlpha
  blank_not_in_inputAlpha := H.blank_not_in_inputAlpha
  δ := H.δ
  q₀ := H.q₀
  qAccept := H.qReject
  qReject := H.qAccept
  qReject_ne_qAccept := H.qReject_ne_qAccept.symm

end TuringMachine
end TuringMachine
end Decidability
