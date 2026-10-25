/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/HierarchyTheorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Structure.v1.Atlas.TheoryOfComputation.code.HierarchyTheorems


namespace HierarchyTheorems

open TuringMachine

/--
The **diagonal language** with respect to an encoding `encode : TMDesc Γ → List Γ`:
the set of strings `w` such that whenever `w` encodes some machine description `d`,
`d.machine` does *not* accept `w`. By Cantor-style diagonalization, this language
differs from every machine's language on at least one encoding.
-/
def diagLang {Γ : Type} (encode : TMDesc Γ → List Γ) : Set (List Γ) :=
  {w : List Γ | ∀ (d : TMDesc Γ), w = encode d → ¬d.machine.accepts w}

end HierarchyTheorems
