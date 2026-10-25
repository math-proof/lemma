/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/FibonacciPrimitiveDivisor.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Def.NumberTheory.Recurrences.PrimitiveDivisor
import Lemma.Nat.Recurrences.PrimitiveDivisor
import Mathlib.Data.Nat.Fib.Basic
import Lemma.Nat.Padics.FibonomialPrimePowerValuation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination


namespace MetaMathlibExt

open scoped BigOperators

/-- N7 auxiliary: the positive Möbius part of the Fibonacci primitive part. -/
def fibMoebiusPos (n : ℕ) : ℕ :=
  ∏ x ∈ n.divisorsAntidiagonal, Nat.fib x.2 ^ (ArithmeticFunction.moebius x.1).toNat

/-- N7 auxiliary: the negative Möbius part of the Fibonacci primitive part. -/
def fibMoebiusNeg (n : ℕ) : ℕ :=
  ∏ x ∈ n.divisorsAntidiagonal, Nat.fib x.2 ^ (-ArithmeticFunction.moebius x.1).toNat

end MetaMathlibExt
