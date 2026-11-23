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
public import Structure.v1.Atlas.TheoryOfComputation.code.SharpSATCoNPHard

@[expose] public section

namespace NPCompleteness

open TuringMachine

section CoNPHardness

variable (enc : SharpSATEncoding)

/--
The `#SAT` language as a set of encoded instances over the alphabet
`BoolFormula`: `w` is accepted iff it decodes to a pair `⟨φ, k⟩` with
`k = countSat φ`.
-/
def SharpSATLang : Set (List BoolFormula) :=
  {w | ∃ φ k, enc.decode w = some (φ, k) ∧ k = φ.countSat}

/--
The reduction `UNSAT ≤_P #SAT`: given an input encoding a single Boolean
formula `φ` (the natural input format for UNSAT), output the `#SAT` encoding of
`⟨φ, 0⟩`. Malformed inputs are mapped to the encoding of `⟨false, 0⟩` (which is
trivially a true `#SAT` instance, but the original input is also not in `UNSAT`
under this convention).
-/
noncomputable def unsatToSharpSAT (w : List BoolFormula) : List BoolFormula :=
  match w with
  | [φ] => enc.encode (φ, 0)
  | _ => enc.encode (BoolFormula.falseConst, 0)

end CoNPHardness
end NPCompleteness
