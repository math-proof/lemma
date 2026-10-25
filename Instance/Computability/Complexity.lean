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
import Theorem.Computability.Complexity.Part2
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

namespace BitstringEncoding

variable {α β : Type*}

/-- `Bool` is encoded as a singleton bitstring. -/
instance : BitstringEncoding Bool where
  encode b := [b]
  decode l := match l with
    | [b] => some b
    | _ => none
  decode_encode _ := rfl

/-- A pair is encoded as a self-delimiting block for the first component
followed by the encoding of the second. -/
instance [BitstringEncoding α] [BitstringEncoding β] : BitstringEncoding (α × β) where
  encode p := delimit (bitEncode p.1) ++ bitEncode p.2
  decode input :=
    match undelimit input with
    | none => none
    | some (block, rest) =>
      match bitDecode block, bitDecode rest with
      | some a, some b => some (a, b)
      | _, _ => none
  decode_encode p := by simp

/-- A list is encoded as the concatenation of self-delimiting blocks for its
elements. -/
instance [BitstringEncoding α] : BitstringEncoding (List α) where
  encode l := ((l.map bitEncode).map delimit).flatten
  decode input := (undelimitBlocks input).bind (·.mapM bitDecode)
  decode_encode l := by
    rw [undelimitBlocks_flatten_delimit (l.map bitEncode)]
    exact mapM_bitDecode_map_bitEncode l

end BitstringEncoding
end MetaMathlibExt
