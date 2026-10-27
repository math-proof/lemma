/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Theorem.Analysis.SpecialFunctions.Part1Ch5Entry30Secondordereulerian.Part2
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 30

Squarefree and non-squarefree Dirichlet series via ζ(s) and ζ(2s).
-/


namespace Ramanujan.Part1Ch5

namespace Entry30Secondordereulerian

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def e30Fmu (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (((n : ℕ) : ℂ) ^ (-s))

end
end Entry30Secondordereulerian
end Ramanujan.Part1Ch5
