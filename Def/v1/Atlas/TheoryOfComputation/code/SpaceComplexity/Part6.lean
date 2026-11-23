/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.BigOperators
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.TuringMachines
public import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
public import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
public import Def.v1.Atlas.TheoryOfComputation.code.GeographyGame.Part2
public import Structure.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part3

@[expose] public section

open Computability
open TuringMachine


namespace SpaceComplexity

/-- The Generalized Geography language `GG = {⟨G, a⟩ | Player I has a forced win on G
starting at a}`, encoded over `Γ`. -/
def ggLanguage {Γ : Type} [Inhabited Γ] (enc : GGEncoding Γ) : Set (List Γ) :=
  {s | ∃ p : Digraph enc.V × enc.V,
    enc.encode p = s ∧ @GeographyGame.GG enc.V enc.decEqV p.1 p.2}


/-- State type for the GG-recognizing NTM: a control bit plus a buffer holding the input
read so far. -/
def GGState (Γ : Type) := Fin 3 × List Γ

end SpaceComplexity
