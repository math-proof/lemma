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
import Def.v1.Atlas.TheoryOfComputation.code.Decidability.Part2


namespace Decidability

namespace TuringMachine

variable {Γ : Type}

/-- A `TMEncoding` over alphabet `Γ` is a bundle of all the encoding/universal-machine
machinery used informally in Sipser. It provides:
* an injective encoding `encode : TMDesc Γ → List Γ` with a decoder,
* a self-reference principle (used for the Recursion Theorem / diagonal argument),
* a universal TM `U` that simulates encoded TMs whenever they halt,
* sequential composition of a decider with another TM, and
* transducer composition with computable functions, as used in mapping reductions. -/
structure TuringMachine.TMEncoding (Γ : Type) where
  encode : TuringMachine.TMDesc Γ → List Γ
  decode : List Γ → Option (TuringMachine.TMDesc Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d
  selfRef : ∀ {Q₀ : Type} [DecidableEq Q₀] (M : TuringMachine.TM Q₀ Γ),
    ∃ d : TuringMachine.TMDesc Γ,
      d.accepts ↔ @TuringMachine.TM.accepts Q₀ Γ _ M (encode d)
  universalSim : ∃ (QU : Type) (_ : DecidableEq QU) (U : TuringMachine.TM QU Γ),
    (∀ d : TuringMachine.TMDesc Γ, d.halts →
      @TuringMachine.TM.halts QU Γ _ U (encode d)) ∧
    (∀ d : TuringMachine.TMDesc Γ, d.halts →
      (@TuringMachine.TM.accepts QU Γ _ U (encode d) ↔ d.accepts)) ∧
    (∀ s, @TuringMachine.TM.accepts QU Γ _ U s →
      ∃ d : TuringMachine.TMDesc Γ, encode d = s ∧ d.accepts)
  sequentialComposition : ∀ {QR QU : Type}
    [DecidableEq QR] [DecidableEq QU]
    (R : TuringMachine.TM QR Γ) (U : TuringMachine.TM QU Γ),
    R.isDecider →
    (∀ w, @TuringMachine.TM.accepts QR Γ _ R w →
      @TuringMachine.TM.halts QU Γ _ U w) →
    ∃ (QS : Type) (_ : DecidableEq QS) (S : TuringMachine.TM QS Γ),
      S.isDecider ∧
      (∀ w, @TuringMachine.TM.accepts QS Γ _ S w ↔
        (@TuringMachine.TM.accepts QR Γ _ R w ∧
         @TuringMachine.TM.accepts QU Γ _ U w))
  transducerComposition : ∀ (f : List Γ → List Γ),
    TuringMachine.IsComputableFunction f →
    ∀ {QR : Type} [DecidableEq QR] (R : TuringMachine.TM QR Γ),
    R.isDecider →
    ∃ (QS : Type) (_ : DecidableEq QS) (S : TuringMachine.TM QS Γ),
      S.isDecider ∧
      (∀ w, @TuringMachine.TM.accepts QS Γ _ S w ↔
        @TuringMachine.TM.accepts QR Γ _ R (f w))

end TuringMachine
end Decidability
