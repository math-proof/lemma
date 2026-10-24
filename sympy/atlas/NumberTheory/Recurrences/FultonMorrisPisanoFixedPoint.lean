/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/FultonMorrisPisanoFixedPoint.lean -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lemma.Nat.Padics.FibonacciFiveAdicValuation
import sympy.atlas.NumberTheory.Recurrences.FibonacciPrimeDivisibility
import Lemma.Nat.Recurrences.FibonacciPrimeDivisibility
namespace MetaMathlibExt

section
-- Helper infrastructure (Steps 1-3 of the proof sketch).
-- `PisanoRet n t` is the `R_n(t)` predicate from the sketch.
/-- Return predicate: the Fibonacci pair has returned to (0,1) mod n at time t. -/
private def PisanoRet (n t : ℕ) : Prop :=
  Nat.ModEq n (Nat.fib t) 0 ∧ Nat.ModEq n (Nat.fib (t + 1)) 1
end
end MetaMathlibExt
