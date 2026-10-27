/-
Author: @akiezun, Avocado
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Tactic.NormNum.NatFactorial
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 1

Unique (1-2ⁿ)Bₙ/n! solution of a shift-plus-derivative identity.
-/


namespace Ramanujan.Part1Ch5

namespace Entry1Euleriangf

open scoped Nat Real BigOperators Interval Polynomial

open Filter Finset Complex Topology

noncomputable section

def chapter5DerivativeExpansion {R : Type*} [Semiring R]
    (a : ℕ → R) (h : R) (phi : R[X]) : R[X] :=
  ∑ n ∈ range (phi.natDegree + 1),
    Polynomial.C (a n * h ^ n) * (Polynomial.derivative^[n]) phi

def chapter5Entry1PlusCoeff (n : ℕ) : ℝ :=
  (1 - (2 : ℝ) ^ n) * (bernoulli n : ℝ) / (n.factorial : ℝ)

/-- The source's shift `p(x) ↦ p(x + h)`. It is `Polynomial.taylor h p` (see
`chapter5PolynomialShift_eq_taylor`); the name is kept because the frozen `Wanted` statement uses
it. -/
def chapter5PolynomialShift {R : Type*} [Semiring R]
    (h : R) (p : R[X]) : R[X] :=
  p.comp (Polynomial.X + Polynomial.C h)

end
end Entry1Euleriangf
end Ramanujan.Part1Ch5
