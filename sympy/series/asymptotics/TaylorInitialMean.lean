
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Initial segment mean for Taylor's variance-to-mean power law

Formalizes the mean of the first `n` terms of an integer sequence.
-/


namespace MetaMathlibExt

open scoped BigOperators

/-- Initial-segment mean `m(a, n)` from Eq. (`eq:mean`): `(1 / n)` times the sum
of `a(j)` over `j = 1, ..., n`, coerced to `ℝ`.

Source: Joel E. Cohen, *Variance Functions of Asymptotically Exponentially
Increasing Integer Sequences Go Beyond Taylor's Law*, Journal of Integer
Sequences 25 (2022), Article 22.9.3, mean/variance definitions, lines 119–124,
equation `eq:mean` at line 122,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Cohen/cohen13.tex>.

Total in Lean (`n = 0` gives `0` via inverse-zero); the source invokes it for
`n ≥ 2` with `ℕ = {1, 2, ...}`. -/
noncomputable def initialSegmentMean (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (a (j + 1) : ℝ)

end MetaMathlibExt

