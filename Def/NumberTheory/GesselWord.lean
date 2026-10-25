/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GesselWord.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Abbrev.NumberTheory.GesselWord
/-!
# Gessel words

A Gessel word over `S = [n]` is a word over the unbarred and barred copies of
`S` whose reverse-label balance is nonnegative on every prefix.

## References

- [A. Ayyer, *Towards a Human Proof of Gessel's Conjecture*](https://cs.uwaterloo.ca/journals/JIS/VOL12/Ayyer/ayyer7.tex),
  Definition 2 (source statement `jis_610953010c03e4ea40bfef6d`).
-/


namespace MetaMathlibExt

open scoped BigOperators

/-- The number of occurrences of the unbarred letter labeled `m` in `w`. -/
def gesselUnbarredCount (n : ℕ) (w : List (GesselAlphabet n)) (m : ℕ) : ℕ :=
  (w.filter fun a => match a with
    | Sum.inl j => decide (j.val + 1 = m)
    | Sum.inr _ => false).length

/-- The number of occurrences of the barred letter labeled `m` in `w`. -/
def gesselBarredCount (n : ℕ) (w : List (GesselAlphabet n)) (m : ℕ) : ℕ :=
  (w.filter fun a => match a with
    | Sum.inl _ => false
    | Sum.inr j => decide (j.val + 1 = m)).length

/-- The signed balance of the unbarred and barred occurrences of the letter labeled `m`. -/
def gesselBalance (n : ℕ) (w : List (GesselAlphabet n)) (m : ℕ) : ℤ :=
  (gesselUnbarredCount n w m : ℤ) - (gesselBarredCount n w m : ℤ)

/-- A Gessel word over `S = [n]`.

For every prefix `w'` and every `1 ≤ k ≤ n`, the sum of the signed balances of the
last `k` labels `n, n - 1, …, n + 1 - k` is nonnegative. -/
def IsGesselWord (n : ℕ) (w : List (GesselAlphabet n)) : Prop :=
  ∀ (w' suffix : List (GesselAlphabet n)), w' ++ suffix = w →
    ∀ k : ℕ, 1 ≤ k → k ≤ n →
      0 ≤ ∑ i ∈ Finset.Icc 1 k, gesselBalance n w' (n + 1 - i)

end MetaMathlibExt
