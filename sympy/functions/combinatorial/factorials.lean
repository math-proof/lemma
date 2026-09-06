import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer

export Nat (factorial)
notation:10000 n "!" => Nat.factorial n

open Polynomial

/-- Rising factorial \(x^{\overline{k}} = x(x+1)\cdots(x+k-1)\). -/
noncomputable def ascFactorial [Semiring α] (x : α) (k : ℕ) : α :=
  (ascPochhammer α k).eval x

noncomputable def descFactorial [Ring α] (x : α) (k : ℕ) : α :=
  (descPochhammer α k).eval x
