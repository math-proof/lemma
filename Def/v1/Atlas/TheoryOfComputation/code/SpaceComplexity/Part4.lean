/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.BigOperators
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
import Def.v1.Atlas.TheoryOfComputation.code.GeographyGame.Part2
import Structure.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part2
open Computability
open TuringMachine


namespace SpaceComplexity

variable {α : Type*}

/-- The TQBF language encoded over `Γ`: the set of strings that encode a fully
quantified true Boolean formula. -/
def tqbfLanguage {Γ : Type} [Inhabited Γ] (enc : QBFEncoding Γ) : Set (List Γ) :=
  {s | ∃ ψ : QBF, enc.encode ψ = s ∧ ψ ∈ TQBF}

/-- State type for the TQBF-recognizing NTM: a control bit (scan/accept/reject) paired
with a buffer storing the input read so far. -/
def TQBFState (Γ : Type) := Fin 3 × List Γ

end SpaceComplexity
