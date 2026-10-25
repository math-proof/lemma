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

/-- A canonical encoding of a type as bitstrings (`List Bool`).
This is a class version of Mathlib's `Computability.Encoding`, specialized to
the alphabet `Bool`. Inlined from FormalConjectures (absent from Mathlib). -/
class BitstringEncoding α extends Computability.Encoding α Bool

end MetaMathlibExt
