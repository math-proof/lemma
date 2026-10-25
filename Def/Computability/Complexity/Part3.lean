/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Computability/Complexity.lean -/

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
/-
# Basic computational-complexity definitions
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Encoding
import Mathlib.Computability.TuringMachine.Computable
import Abbrev.Computability.Complexity
/-! A bitstring-specialized encoding API and basic definitions of `P`, `NP`,
and `coNP`.

This file adapts selected definitions from the following Apache-2.0 sources at
commit `62f56e8e4dab933a720f649721875c478b0ecf1c`:

* [`FormalConjecturesForMathlib/Computability/BitstringEncoding.lean`](https://github.com/google-deepmind/formal-conjectures/blob/62f56e8e4dab933a720f649721875c478b0ecf1c/FormalConjecturesForMathlib/Computability/BitstringEncoding.lean)
* [`FormalConjecturesForMathlib/Computability/Complexity.lean`](https://github.com/google-deepmind/formal-conjectures/blob/62f56e8e4dab933a720f649721875c478b0ecf1c/FormalConjecturesForMathlib/Computability/Complexity.lean)

Local changes combine the selected APIs into one module, place them under
`MetaMathlibExt`, provide self-delimiting `Bool`, product, and list encodings,
and omit unrelated source instances and lemmas.
-/


namespace MetaMathlibExt

open Computability

namespace ComplexityTheory

/-- `IsPolyTimeWithEncoding ea eb f` asserts that `f` is computable in
polynomial time under the given encodings. Inlined from FormalConjectures
(absent from Mathlib). -/
def IsPolyTimeWithEncoding {α β Γα Γβ : Type} (ea : Encoding α Γα)
    (eb : Encoding β Γβ) (f : α → β) :=
  Nonempty (Turing.TM2ComputableInPolyTime ea.encode eb.encode f)

/-- A function is polynomial-time computable when it is
`IsPolyTimeWithEncoding` for the canonical bitstring encodings. Inlined from
FormalConjectures (absent from Mathlib). -/
def IsPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) : Prop :=
  IsPolyTimeWithEncoding (BitstringEncoding.toEncoding (α := α))
    (BitstringEncoding.toEncoding (α := β)) f

/-- The class P: decision problems decidable in polynomial time by a
deterministic Turing machine. Inlined from FormalConjectures (absent from
Mathlib). -/
def P : DecisionComplexityClass :=
  { L | IsPolyTime L }

/-- The class NP: decision problems with a polynomial bound `p` and a poly-time
verifier `R` such that `L x` iff some witness `w` of length at most `p |x|` is
accepted. Inlined from FormalConjectures (absent from Mathlib). -/
def NP : DecisionComplexityClass :=
  { L | ∃ (p : Polynomial ℕ), ∃ R : (List Bool × List Bool) → Bool,
      IsPolyTime R ∧
      ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ R (x, w) }

/-- The class coNP: decision problems whose complements are in NP. Inlined
from FormalConjectures (absent from Mathlib). -/
def coNP : DecisionComplexityClass :=
  { L | Lᶜ ∈ NP }

end ComplexityTheory
end MetaMathlibExt
