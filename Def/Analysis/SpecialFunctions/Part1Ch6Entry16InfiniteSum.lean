/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 16

Infinite sum of rᵏ/(1-axᵏ) splits into two related convergent series.
-/


namespace Ramanujan.Part1Ch6

namespace Entry16InfiniteSum

open scoped Nat Real BigOperators Interval Polynomial

open Asymptotics Filter Finset Complex Topology

noncomputable section

def chapter6Entry16LeftTerm (a r x : ℂ) (j : ℕ) : ℂ :=
  let k := j + 1
  r ^ k / (1 - a * x ^ k)

def chapter6Entry16MiddleTerm (a r x : ℂ) (j : ℕ) : ℂ :=
  let k := j + 1
  (a * r * x ^ k) ^ k / (1 - a * x ^ k)

def chapter6Entry16RightTerm (a r x : ℂ) (j : ℕ) : ℂ :=
  let k := j + 1
  a ^ (k - 1) * r ^ k * x ^ ((k - 1) * k) /
    (1 - r * x ^ (k - 1))

/-- Triangle summand for the double-sum argument:
`triFun a r x n m = a ^ n * r ^ (m + 1) * x ^ ((m + 1) * n)` on `n ≤ m`. -/
def triFun (a r x : ℂ) (n m : ℕ) : ℂ :=
  if n ≤ m then a ^ n * r ^ (m + 1) * x ^ ((m + 1) * n) else 0

/-- Uniform majorant for the column sums. -/
def triBound (a r x : ℂ) (n : ℕ) : ℝ :=
  ‖r‖ / (1 - ‖r‖) * (‖a‖ * ‖r‖ * ‖x‖ ^ (n + 1)) ^ n

end
end Entry16InfiniteSum
end Ramanujan.Part1Ch6
