/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zeta4.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Def.Analysis.Ramanujan.Part1Ch7Entry10ZetaSide
import Lemma.Real.Ramanujan.Part1Ch7Entry10ZetaSide
import Mathlib.Analysis.Meromorphic.Complex
import Lemma.Nat.LSeries.RiemannZeta
/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 10

Bernoulli-Gamma-sine expression equals (1-nʳ⁺¹)ζ(-r) meromorphically.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry10Zeta4

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7BernoulliStar (z : ℂ) : ℂ :=
  2 * Complex.Gamma (z + 1) * riemannZeta z /
    Complex.cpow (2 * (Real.pi : ℂ)) z

def chapter7Entry10BernoulliSide (n : ℕ) (r : ℂ) : ℂ :=
  (Complex.cpow (n : ℂ) (r + 1) - 1) *
    Complex.sin ((Real.pi : ℂ) * r / 2) * chapter7BernoulliStar (r + 1) /
      (r + 1)

def chapter7BadSet : Set ℂ := {0} ∪ Set.range (fun k : ℕ => (-1 - (k : ℂ)))

end
end Entry10Zeta4
end MathlibExt.Analysis.Ramanujan.Part1Ch7
