/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KeithNumber.lean -/

import Mathlib.Data.Nat.Basic


namespace MetaMathlibExt

/-- Extend a list of decimal digits by repeatedly appending the sum of the
previous `digits.length` entries. This is the recurrence used for Keith
numbers.

Source: Martin Klazar and Florian Luca, *Counting Keith Numbers*, Journal of
Integer Sequences 10 (2007), Definition in the introduction. -/
def keithSequencePrefix (digits : List ℕ) : ℕ → List ℕ
  | 0 => digits
  | k + 1 =>
    let values := keithSequencePrefix digits k
    values ++ [(values.drop (values.length - digits.length)).foldl (· + ·) 0]

/-- The zero-indexed Keith sequence whose initial entries are `digits`.

After the initial entries, each term is the sum of the preceding
`digits.length` terms. -/
def keithSequence (digits : List ℕ) (m : ℕ) : ℕ :=
  (keithSequencePrefix digits (m + 1 - digits.length)).getD m 0

/-- `IsKeithNumberWithDigits N digits` says that `digits` is the ordinary
decimal representation of `N` and that `N` occurs after those digits in its
Keith sequence.

Source: Martin Klazar and Florian Luca, *Counting Keith Numbers*, Journal of
Integer Sequences 10 (2007), Definition in the introduction. -/
def IsKeithNumberWithDigits (N : ℕ) (digits : List ℕ) : Prop :=
  2 ≤ digits.length ∧
    (∀ d ∈ digits, d < 10) ∧
    digits.head? ≠ some 0 ∧
    digits.foldl (fun acc d => acc * 10 + d) 0 = N ∧
    ∃ m, digits.length ≤ m ∧ keithSequence digits m = N

/-- A Keith number is a positive integer with at least two decimal digits that
occurs in the sequence initialized by those digits and continued by summing the
preceding fixed-size window.

Source: Martin Klazar and Florian Luca, *Counting Keith Numbers*, Journal of
Integer Sequences 10 (2007), Definition in the introduction. -/
def IsKeithNumber (N : ℕ) : Prop :=
  ∃ digits, IsKeithNumberWithDigits N digits

end MetaMathlibExt
