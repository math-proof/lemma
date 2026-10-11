
import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt


/-- Admissible sequences for Taylor's variance-to-mean power law: sequences
over indices 1, 2, ... (the value at 0 is ignored), positive at every
positive index, and eventually strictly increasing.

Source: Joel E. Cohen, *Variance Functions of Asymptotically Exponentially
Increasing Integer Sequences Go Beyond Taylor's Law*, Journal of Integer
Sequences 25 (2022), Article 22.9.3, the collection `𝒜` of infinite
eventually strictly increasing sequences of natural numbers, lines 113–125,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Cohen/cohen13.tex>. -/
def IsTaylorAdmissibleSequence (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < n → 0 < a n) ∧ ∃ n₀, 1 ≤ n₀ ∧ ∀ n, n₀ ≤ n → a n < a (n + 1)


end MetaMathlibExt
