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
import Instance.v1.Atlas.TheoryOfComputation.code.Decidability.Part2


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
