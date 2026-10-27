/-
Author: @akiezun, Avocado
-/

import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Theorem.Analysis.SpecialFunctions.Part1Ch5Entry10bEuleriansymmetry.Part2
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

def berB : PowerSeries ℚ := bernoulliPowerSeries ℚ

def berB2 : PowerSeries ℚ := (PowerSeries.rescale 2) berB

def berB4 : PowerSeries ℚ := (PowerSeries.rescale 4) berB

def tanhPS : PowerSeries ℚ := sinhPS * eulerEGF

end
end Entry10bEuleriansymmetry
end Ramanujan.Part1Ch5
end
