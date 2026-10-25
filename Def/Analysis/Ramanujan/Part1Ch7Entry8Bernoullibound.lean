/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry8Bernoullibound.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Def.Analysis.Ramanujan.Part1Ch7Phi
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Theorem.Analysis.Ramanujan.Part1Ch7Entry8
import Lemma.Complex.Part1Ch7Entry8
/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 8

Berndt's `φ_r(x)` (`chapter7Phi`) for a positive integer `r` is the polynomial
`(B_{r+1}(x + 1) - B_{r+1}(1)) / (r + 1)`, which expands in Bernoulli numbers and in
zeta values at negative odd integers, and gives Faulhaber's power sums at natural `x`.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry8Bernoullibound

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7BernoulliPolynomial (m : ℕ) (x : ℂ) : ℂ :=
  ((Polynomial.bernoulli m).map (algebraMap ℚ ℂ)).eval x

def chapter7Entry8BernoulliForm (r : ℕ) (x : ℂ) : ℂ :=
  (∑ k ∈ range (r + 1),
      ((r + 1).choose k : ℂ) * (bernoulli k : ℂ) * x ^ (r + 1 - k)) /
      (r + 1 : ℂ) +
    x ^ r

def chapter7Entry8ZetaForm (r : ℕ) (x : ℂ) : ℂ :=
  x ^ (r + 1) / (r + 1 : ℂ) + x ^ r / 2 -
    2 / (r + 1 : ℂ) *
      ∑ k ∈ Icc 1 (r / 2),
        ((r + 1).choose (2 * k) : ℂ) * (k : ℂ) *
          riemannZeta (1 - (2 * k : ℂ)) * x ^ (r + 1 - 2 * k)

/-- The polynomial `(B_{r+1}(x + 1) - B_{r+1}(1)) / (r + 1)`, which extends Berndt's `φ_r` to
all of `ℂ`; `chapter7Phi_eq_chapter7IntegerPhi` shows it agrees with `chapter7Phi` on `-1 < x < 0`.
-/
def chapter7IntegerPhi (r : ℕ) (x : ℂ) : ℂ :=
  (chapter7BernoulliPolynomial (r + 1) (x + 1) -
      chapter7BernoulliPolynomial (r + 1) 1) /
    (r + 1 : ℂ)

end
end Entry8Bernoullibound
end MathlibExt.Analysis.Ramanujan.Part1Ch7
