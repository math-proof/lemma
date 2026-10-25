/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CommaSequence.lean -/

import Mathlib.Data.Nat.Log


namespace MetaMathlibExt

/-- Most significant base-`b` digit for `0 < m`, given by `m / b ^ Nat.log b m`
(source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`). -/
def commaMsd (b m : Nat) : Nat :=
  m / b ^ Nat.log b m

/-- Finite candidate digit for the generalized comma step: with `x = n % b`
the least significant digit, `m = n + b * (n % b) + y.val` is the next value
and `y` is its most significant digit
(source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`). -/
def IsCommaCandidate (b n : Nat) (y : Fin b) : Prop :=
  let m := n + b * (n % b) + y.val
  0 < m ∧ commaMsd b m = y.val

/-- Comma-successor relation: `m = n + b * (n % b) + y.val` for a candidate `y`,
minimal over every smaller digit, so smallest `y` is exactly the lexicographically
earliest next value (source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`). -/
def IsCommaSucc (b n m : Nat) : Prop :=
  ∃ y : Fin b, IsCommaCandidate b n y ∧ m = n + b * (n % b) + y.val ∧
    ∀ y' : Fin b, y'.val < y.val → ¬ IsCommaCandidate b n y'

/-- Terminal value: absence of any candidate digit
(source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`). -/
def IsCommaTerminal (b n : Nat) : Prop :=
  ∀ y : Fin b, ¬ IsCommaCandidate b n y

/-- Infinite comma sequence with one-based indexing `a 1 = v`, requiring
valid base `2 ≤ b` and positive initial value `0 < v`
(source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`). -/
def IsInfiniteCommaSeq (b v : Nat) (a : Nat → Nat) : Prop :=
  2 ≤ b ∧ 0 < v ∧ a 1 = v ∧ ∀ n, 1 ≤ n → IsCommaSucc b (a n) (a (n + 1))

/-- Termination as absence of any infinite comma sequence, requiring valid base
`2 ≤ b` and positive initial value `0 < v`
(source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`). -/
def IsCommaTerminating (b v : Nat) : Prop :=
  2 ≤ b ∧ 0 < v ∧ ¬ ∃ a : Nat → Nat, IsInfiniteCommaSeq b v a

end MetaMathlibExt
