/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean -/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Int.SuccPred
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

def Cext (t : ℕ) (m : ℤ) : ℤ := if 0 ≤ m then (Nat.choose t m.toNat : ℤ) else 0

def Aa (n : ℕ) (i : ℤ) : ℤ := Cext (2*n) ((n:ℤ) + i)

def Bb (n : ℕ) (i : ℤ) : ℤ := Cext (2*n-2) ((n:ℤ) - 1 + i)

def gg (n : ℕ) (i j : ℤ) : ℤ := Aa n i * Bb n j - Bb n i * Aa n j

def KK (n : ℕ) (i j : ℤ) : ℤ := Bb n i * Bb n (j-1) - Bb n (i-1) * Bb n j

def Qn (n m : ℕ) : ℤ := ∑ j ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), KK n (m:ℤ) j

def Phi (n N : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (N+1), ∑ j ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), gg n (m:ℤ) j

def Sbox (n N : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
    Aa n i * Aa n j * |i^2 - j^2|

def Wbox (n N : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
    Aa n i * Aa n j * max (i^2 - j^2) 0

def coneSum (n N : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc (0:ℤ) (N:ℤ), ∑ j ∈ Finset.Icc (-i) i,
    Aa n i * Aa n j * (i^2 - j^2)

end MetaMathlibExt
