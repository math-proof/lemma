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

namespace MetaMathlibExt

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

open Computability

/-- A canonical encoding of a type as bitstrings (`List Bool`).
This is a class version of Mathlib's `Computability.Encoding`, specialized to
the alphabet `Bool`. Inlined from FormalConjectures (absent from Mathlib). -/
class BitstringEncoding α extends Computability.Encoding α Bool

namespace BitstringEncoding

variable {α β : Type*}

/-- The encoding function of the canonical `BitstringEncoding` of `α`. -/
def bitEncode [BitstringEncoding α] (a : α) : List Bool := toEncoding.encode a

/-- The decoding function of the canonical `BitstringEncoding` of `α`. -/
def bitDecode [BitstringEncoding α] (l : List Bool) : Option α := toEncoding.decode l

/-- Decoding is a left inverse of encoding. -/
@[simp]
theorem bitDecode_bitEncode [BitstringEncoding α] (a : α) :
    bitDecode (bitEncode a) = some a :=
  toEncoding.decode_encode a

/-- Make a bitstring self-delimiting: each payload bit `b` becomes the two bits
`[true, b]`, and the block is terminated by `false`. -/
def delimit : List Bool → List Bool
  | [] => [false]
  | b :: l => true :: b :: delimit l

/-- Parse one self-delimiting block from the front of the input, returning the
payload and the remaining input. -/
def undelimit : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: input => (undelimit input).map fun p => (b :: p.1, p.2)
  | _ => none

@[simp]
theorem undelimit_delimit (l rest : List Bool) :
    undelimit (delimit l ++ rest) = some (l, rest) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, undelimit, ih]

@[simp]
theorem length_delimit (l : List Bool) :
    (delimit l).length = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, ih]; omega

/-- Parse a sequence of self-delimiting blocks off the front of the input,
using `fuel` to bound the number of blocks. -/
def undelimitBlocksAux : ℕ → List Bool → Option (List (List Bool))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, input =>
    (undelimit input).bind fun p => (undelimitBlocksAux fuel p.2).map (p.1 :: ·)

/-- Parse a sequence of self-delimiting blocks off the front of the input. -/
def undelimitBlocks (input : List Bool) : Option (List (List Bool)) :=
  undelimitBlocksAux input.length input

theorem length_le_length_flatten_delimit (l : List (List Bool)) :
    l.length ≤ ((l.map delimit).flatten).length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      length_delimit]
    omega

private theorem undelimitBlocksAux_flatten_delimit (l : List (List Bool)) (fuel : ℕ)
    (hfuel : l.length ≤ fuel) :
    undelimitBlocksAux fuel ((l.map delimit).flatten) = some l := by
  induction l generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons b t ih =>
    rw [List.length_cons] at hfuel
    cases fuel <;> cases b <;> grind [delimit, undelimitBlocksAux, undelimit_delimit]

theorem undelimitBlocks_flatten_delimit (l : List (List Bool)) :
    undelimitBlocks ((l.map delimit).flatten) = some l :=
  undelimitBlocksAux_flatten_delimit l _ (length_le_length_flatten_delimit l)

@[simp]
theorem mapM_bitDecode_map_bitEncode [BitstringEncoding α] (l : List α) :
    (l.map bitEncode).mapM bitDecode = some l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

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

namespace ComplexityTheory

/-- The type of decision problems: functions from lists of booleans to
booleans. Inlined from FormalConjectures (absent from Mathlib). -/
abbrev DecisionProblem := List Bool → Bool

/-- The type of complexity classes: sets of decision problems. Inlined from
FormalConjectures (absent from Mathlib). -/
abbrev DecisionComplexityClass := Set DecisionProblem

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
