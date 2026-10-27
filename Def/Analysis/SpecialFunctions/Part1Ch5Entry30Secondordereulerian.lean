/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 30

Squarefree and non-squarefree Dirichlet series via ζ(s) and ζ(2s).
-/


namespace Ramanujan.Part1Ch5

namespace Entry30Secondordereulerian

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

/-- The local factor at a prime `p` with exponent `e`: `1` for `e = 0`, `a p` for `e = 1`,
and `0` for `e ≥ 2`. -/
def chapter5Entry30LocalCoeff (a : ℕ → ℂ) (p e : ℕ) : ℂ :=
  match e with
  | 0 => 1
  | 1 => a p
  | _ + 2 => 0

/-- The multiplicative coefficient with local factors `chapter5Entry30LocalCoeff a`: `0` at
`n = 0`, otherwise the product of the local factors over the prime factors of `n`. -/
def chapter5Entry30Coeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else ∏ p ∈ n.primeFactors, chapter5Entry30LocalCoeff a p (n.factorization p)

/-- The `j`-th term of `∑ n ^ (-s)` over non-squarefree `n ≥ 1`, indexed by `n = j + 1`. -/
def chapter5Entry30NonSquarefreeTerm (s : ℂ) (j : ℕ) : ℂ :=
  let n := j + 1
  if Squarefree n then 0 else (n : ℂ) ^ (-s)

/-- The `j`-th term of `∑ n ^ (-s)` over squarefree `n ≥ 1` with an odd number of prime
factors, indexed by `n = j + 1`. -/
def chapter5Entry30OddTerm (s : ℂ) (j : ℕ) : ℂ :=
  let n := j + 1
  if Squarefree n ∧ Odd n.primeFactors.card then (n : ℂ) ^ (-s) else 0

/-- `chapter5Entry30Coeff` with local values `a p = -p ^ (-s)`. -/
def chapter5Entry30SignedCoeff (s : ℂ) (n : ℕ) : ℂ :=
  chapter5Entry30Coeff (fun p => -((p : ℂ) ^ (-s))) n

/-- The `j`-th term of `∑ n ^ (-s)` over squarefree `n ≥ 1`, indexed by `n = j + 1`. -/
def chapter5Entry30SquarefreeTerm (s : ℂ) (j : ℕ) : ℂ :=
  let n := j + 1
  if Squarefree n then (n : ℂ) ^ (-s) else 0

end
end Entry30Secondordereulerian
end Ramanujan.Part1Ch5
