/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LadderNSPACE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Structure.v1.Atlas.TheoryOfComputation.code.LadderNSPACE.Part2
open Computability TuringMachine SpaceComplexity


namespace SpaceComplexity

/-- The uniform formulation `LADDER_DFA = {⟨B, u, v⟩ | B is a DFA and there is a ladder in
`L(B)` from `u` to `v`}` over a fixed tape alphabet, using a `DFAEncoding`. -/
def LADDER_DFA_Uniform (enc : DFAEncoding) : Set (List enc.Γ) :=
  {w | ∃ (α : Type) (σ : Type) (_ : Fintype α) (_ : DecidableEq α)
         (_ : Fintype σ) (_ : DecidableEq σ)
         (B : DFA α σ) (u v : List α),
       w = enc.encode B u v ∧ LADDER_DFA B u v}


end SpaceComplexity
