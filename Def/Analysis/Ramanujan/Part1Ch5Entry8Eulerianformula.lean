/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry8Eulerianformula.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Def.Analysis.Ramanujan.Part1Ch5Entry4
import Lemma.Complex.Part1Ch5Entry4
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 8

Entry 8 from B. C. Berndt, *Ramanujan's Notebooks, Part I* (Springer, 1985):
evaluations of the Eulerian polynomial `chapter5Psi` at `-1` and `1`, and the
two power series for `1 / (Complex.exp z + 1)` in terms of Bernoulli numbers
and Eulerian polynomials.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry8Eulerianformula

open scoped Nat Real BigOperators Polynomial ContDiff

open Filter Finset Complex Topology Entry4

open PowerSeries

noncomputable section

def chapter5Entry8BernoulliTerm (z : ℂ) (j : ℕ) : ℂ :=
  (1 - (2 : ℂ) ^ (j + 1)) * (bernoulli (j + 1) : ℂ) * z ^ j /
    ((j + 1).factorial : ℂ)

def chapter5Entry8PsiTerm (z : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n * chapter5Psi n (1 : ℂ) * z ^ n /
    ((2 : ℂ) ^ (n + 1) * (n.factorial : ℂ))

noncomputable def psL : PowerSeries ℂ :=
  PowerSeries.mk fun n => (1 - (2 : ℂ) ^ (n + 1)) * (bernoulli (n + 1) : ℂ) /
      ((n + 1).factorial : ℂ)

noncomputable def auxF : ℂ → ℂ := fun x => 1 / (Complex.exp x + 1)

noncomputable def auxG : ℂ → ℂ := fun x => Complex.exp x + 1

noncomputable def auxT : PowerSeries ℂ :=
  PowerSeries.mk fun n => iteratedDeriv n auxF 0 / (n.factorial : ℂ)

noncomputable def psiPoly (m : ℕ) : Polynomial ℂ :=
  ∑ k ∈ range m, Polynomial.C (eulerianNumber m k : ℂ) * (-Polynomial.X) ^ k

end
end Entry8Eulerianformula
end MathlibExt.Analysis.Ramanujan.Part1Ch5
end
