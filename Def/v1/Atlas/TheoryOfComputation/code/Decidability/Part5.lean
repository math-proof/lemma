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
public import Instance.v1.Atlas.TheoryOfComputation.code.Decidability.Part2

@[expose] public section

namespace Decidability

namespace TuringMachine

variable {Γ : Type}

namespace TuringMachine

variable {Γ : Type}

/-- Map a piece of raw TM data to its language. If `qAccept = qReject` (ill-formed data) the
language is empty; otherwise it is the language of the corresponding `TM`. -/
noncomputable def tmDescToLang (Γ : Type) [DecidableEq Γ] :
    TMDescType Γ → Set (List Γ) :=
  fun ⟨n, blank, δ, q₀, qAccept, qReject⟩ =>
    if h : qReject ≠ qAccept then
      (TM.mk blank ∅ (Set.notMem_empty _) δ q₀ qAccept qReject h : TM (Fin n) Γ).language
    else ∅

end TuringMachine
end TuringMachine
end Decidability
