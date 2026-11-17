/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalDescentPermutations.lean -/

module

public import Mathlib.Data.Set.Function
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Nat.SuccPred

@[expose] public section

namespace MetaMathlibExt

/-! # Minimal descent permutations
-/

def descents (f : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  Finset.filter (fun i => f (i + 1) < f i) (Finset.Icc 1 (n - 1))

def skipIndex (j a : ℕ) : ℕ :=
  if a < j then a else a + 1

def eraseValue (r x : ℕ) : ℕ :=
  if x < r then x else x - 1

def deletePerm (f : ℕ → ℕ) (j a : ℕ) : ℕ :=
  eraseValue (f j) (f (skipIndex j a))

def unskipIndex (j x : ℕ) : ℕ :=
  if x < j then x else x - 1

end MetaMathlibExt
