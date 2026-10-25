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
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part2
open Computability
open TuringMachine


namespace SpaceComplexity

variable {α : Type*}

/-- **Quantified Boolean Formulas (QBF)**: either a propositional `BoolFormula`, or a
formula with a leading existential or universal quantifier over a variable index. -/
inductive QBF : Type where
  | body : BoolFormula → QBF
  | exists_ : ℕ → QBF → QBF
  | forall_ : ℕ → QBF → QBF

end SpaceComplexity
