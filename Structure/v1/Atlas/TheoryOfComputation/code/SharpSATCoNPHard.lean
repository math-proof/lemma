/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATCoNPHard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Lattice.Fold
public import Def.v1.Atlas.TheoryOfComputation.code.SharpSATCoNPHard


public section

namespace NPCompleteness

open TuringMachine

section CoNPHardness

/--
A simple encoding of `#SAT` instances `⟨φ, k⟩` as lists of Boolean formulas,
specifically tailored for the coNP-hardness reduction. Only one round-trip law
is required: `decode (encode p) = some p`.
-/
structure SharpSATEncoding where
  encode : BoolFormula × ℕ → List BoolFormula
  decode : List BoolFormula → Option (BoolFormula × ℕ)
  decode_encode : ∀ p, decode (encode p) = some p

end CoNPHardness
end NPCompleteness
