/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/FibonacciPrimitiveDivisor.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Def.NumberTheory.Recurrences.PrimitiveDivisor
public import Theorem.Nat.Recurrences.PrimitiveDivisor
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

/-- N7 auxiliary: the positive Möbius part of the Fibonacci primitive part. -/
def fibMoebiusPos (n : ℕ) : ℕ :=
  ∏ x ∈ n.divisorsAntidiagonal, Nat.fib x.2 ^ (ArithmeticFunction.moebius x.1).toNat

/-- N7 auxiliary: the negative Möbius part of the Fibonacci primitive part. -/
def fibMoebiusNeg (n : ℕ) : ℕ :=
  ∏ x ∈ n.divisorsAntidiagonal, Nat.fib x.2 ^ (-ArithmeticFunction.moebius x.1).toNat

end MetaMathlibExt
