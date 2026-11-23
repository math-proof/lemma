/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/FultonMorrisPisanoFixedPoint.lean -/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Def.NumberTheory.Recurrences.FibonacciPrimeDivisibility
public import Theorem.Nat.Recurrences.FibonacciPrimeDivisibility

@[expose] public section

namespace MetaMathlibExt

section

-- Helper infrastructure (Steps 1-3 of the proof sketch).
-- `PisanoRet n t` is the `R_n(t)` predicate from the sketch.
/-- Return predicate: the Fibonacci pair has returned to (0,1) mod n at time t. -/
def PisanoRet (n t : ℕ) : Prop :=
  Nat.ModEq n (Nat.fib t) 0 ∧ Nat.ModEq n (Nat.fib (t + 1)) 1

end
end MetaMathlibExt
