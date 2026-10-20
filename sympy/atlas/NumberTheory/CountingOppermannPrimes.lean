/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CountingOppermannPrimes.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Oppermann prime counts

Asymptotic count of primes in the Oppermann intervals `[n^2 - n, n^2]` and
`[n^2, n^2 + n]`.

Concept ID: `jis_sem_b1c5531b893b694777f2c1c5`.
Source statement: `jis_6984ebbf83b6eb73fb1b156d`.
Source: https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.tex
-/

namespace MetaMathlibExt

/-- Number of primes in the closed interval `[n^2 - n, n^2]`.

Concept `jis_sem_b1c5531b893b694777f2c1c5` (counting Oppermann primes),
source statement `jis_6984ebbf83b6eb73fb1b156d`: the count of primes in
`[n^2 - n, n^2]`. Natural subtraction truncates `n ^ 2 - n` to `0` at
`n = 0`; this is invisible to the `atTop` asymptotic. -/
def oppermannLowerPrimeCount (n : ℕ) : ℕ :=
  ((Finset.Icc (n ^ 2 - n) (n ^ 2)).filter Nat.Prime).card

/-- Number of primes in the closed interval `[n^2, n^2 + n]`.

Concept `jis_sem_b1c5531b893b694777f2c1c5` (counting Oppermann primes),
source statement `jis_6984ebbf83b6eb73fb1b156d`: the count of primes in
`[n^2, n^2 + n]`. -/
def oppermannUpperPrimeCount (n : ℕ) : ℕ :=
  ((Finset.Icc (n ^ 2) (n ^ 2 + n)).filter Nat.Prime).card

/-- Asymptotic main term `n / (2 log n)` for the Oppermann prime counts.

Concept `jis_sem_b1c5531b893b694777f2c1c5` (counting Oppermann primes),
source statement `jis_6984ebbf83b6eb73fb1b156d`: the shared asymptotic for
both Oppermann intervals. `Real.log n = 0` at `n = 0, 1`, so the term is
junk-valued there; this is invisible to the `atTop` asymptotic. -/
noncomputable def oppermannAsymptotic (n : ℕ) : ℝ :=
  (n : ℝ) / (2 * Real.log n)

end MetaMathlibExt
