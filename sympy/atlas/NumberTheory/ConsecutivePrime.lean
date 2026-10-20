/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ConsecutivePrime.lean -/

import Mathlib.Data.List.Defs
import Mathlib.Data.Nat.Prime.Basic

namespace MetaMathlibExt

/-- Two natural numbers are consecutive primes when they are prime, strictly ordered, and no
prime lies strictly between them.

This packages the usual meaning of successive primes `pₖ, pₖ₊₁` used in the source papers.

Sources:
* <https://cs.uwaterloo.ca/journals/JIS/VOL25/Krizek/krizek3.tex>
* <https://cs.uwaterloo.ca/journals/JIS/VOL14/Noe/noe12.tex>
* <https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.tex>

JIS concept: `jis_sem_36fb078a6414434f9cc22b4a` ("consecutive prime").
-/
def AreConsecutivePrimes (p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ ∀ r, Nat.Prime r → r ≤ p ∨ q ≤ r

/-- A nonempty, strictly increasing list consisting of a contiguous block of primes.

See the sources cited on `AreConsecutivePrimes` for occurrences of blocks
`pₖ, pₖ₊₁, …, pₘ` of consecutive primes.
-/
def IsConsecutivePrimeBlock (l : List ℕ) : Prop :=
  l ≠ [] ∧ (∀ p ∈ l, Nat.Prime p) ∧ List.Pairwise (· < ·) l ∧
    ∀ x ∈ l.consecutivePairs, AreConsecutivePrimes x.1 x.2

/-- A contiguous block of primes whose entries all satisfy an additional predicate `P`.

This covers, for example, the factorial- and primorial-bounded blocks in the source papers by
choosing the corresponding predicate `P`.
-/
def IsRestrictedConsecutivePrimeBlock (P : ℕ → Prop) (l : List ℕ) : Prop :=
  IsConsecutivePrimeBlock l ∧ ∀ p ∈ l, P p

end MetaMathlibExt
