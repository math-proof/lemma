module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Initialize.Tactic.Attr.Basic

@[expose] public section

open Finset MeasureTheory
open scoped ENNReal Nat


/-- Number of coordinates of `ω` equal to `a`. -/
def countVec {α : Type*} [DecidableEq α] {n : ℕ} (ω : Fin n → α) (a : α) : ℕ :=
  ∑ i, if ω i = a then 1 else 0

def predCount {α : Type*} [DecidableEq α] (c : α → ℕ) (a : α) : α → ℕ :=
  Function.update c a (c a - 1)

def empiricalSet {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ) (c : α → ℕ) :
  Finset (Fin n → α) :=
  {ω | ∀ a, countVec ω a = c a}

end
