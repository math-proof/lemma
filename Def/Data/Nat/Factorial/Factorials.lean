module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Notation.Data.Nat.Factorial.Factorials

@[expose] public section

export Nat (factorial)
open Polynomial


/-- Rising factorial \(x^{\overline{k}} = x(x+1)\cdots(x+k-1)\). -/
noncomputable def ascFactorial [Semiring α] (x : α) (k : ℕ) : α :=
  (ascPochhammer α k).eval x

noncomputable def descFactorial [Ring α] (x : α) (k : ℕ) : α :=
  (descPochhammer α k).eval x

