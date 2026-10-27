/-
Author: @akiezun, Avocado
-/

import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Theorem.Analysis.SpecialFunctions.Part1Ch5Entry10bEuleriansymmetry
/-!
# Ramanujan's Notebooks, Part I, Chapter 5

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch5

namespace Entry10bEuleriansymmetry

open scoped BigOperators

open Finset

noncomputable section

def eulerEGF : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    if n % 2 = 1 then 0
    else (((chapter5EulerEven (n / 2) : ℤ) : ℚ) / (n.factorial : ℚ))

def coshPS : PowerSeries ℚ :=
  (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
    PowerSeries.C (2⁻¹ : ℚ)

def sinhPS : PowerSeries ℚ :=
  (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
    PowerSeries.C (2⁻¹ : ℚ)

end
end Entry10bEuleriansymmetry
end Ramanujan.Part1Ch5
end
