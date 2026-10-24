/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATCoNPHard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TheoryOfComputation.code.SharpSAT
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold

namespace NPCompleteness

open TuringMachine in
/--
A language `B` is `coNP`-hard if every language `A ∈ coNP` polynomial-time
reduces to `B`. Analogous to the NP-hardness definition `∀ A ∈ NP, A ≤_P B`
from the textbook, but for the class `coNP`.
-/
def IsCoNPHard {Γ : Type} (B : Set (List Γ)) : Prop :=
  ∀ A : Set (List Γ), InCoNP A → PolyReducible A B

/--
One plus the largest variable index appearing in `φ`. This gives an upper bound
`m` such that every variable of `φ` has index `< m`.
-/
noncomputable def BoolFormula.maxVarSucc (φ : BoolFormula) : ℕ :=
  (φ.vars.sup id).succ

/-- A Boolean formula `φ` is a tautology iff `φ.eval σ = true` for every
assignment `σ`. -/
def BoolFormula.IsTautology (φ : BoolFormula) : Prop :=
  ∀ σ : BoolAssignment, φ.eval σ = true

/-- The language `TAUTOLOGY = {⟨φ⟩ | φ is a tautology}`, the canonical
coNP-complete language. -/
def TAUTOLOGY : Set BoolFormula :=
  {φ | φ.IsTautology}

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
