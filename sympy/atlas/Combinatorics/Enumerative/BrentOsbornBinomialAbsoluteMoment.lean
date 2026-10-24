/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Data.Int.SuccPred
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

private def Cext (t : ℕ) (m : ℤ) : ℤ := if 0 ≤ m then (Nat.choose t m.toNat : ℤ) else 0

private def Aa (n : ℕ) (i : ℤ) : ℤ := Cext (2*n) ((n:ℤ) + i)
private def Bb (n : ℕ) (i : ℤ) : ℤ := Cext (2*n-2) ((n:ℤ) - 1 + i)

private def gg (n : ℕ) (i j : ℤ) : ℤ := Aa n i * Bb n j - Bb n i * Aa n j
private def KK (n : ℕ) (i j : ℤ) : ℤ := Bb n i * Bb n (j-1) - Bb n (i-1) * Bb n j

private def Qn (n m : ℕ) : ℤ := ∑ j ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), KK n (m:ℤ) j

private def Phi (n N : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (N+1), ∑ j ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), gg n (m:ℤ) j

private def Sbox (n N : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
    Aa n i * Aa n j * |i^2 - j^2|
private def Wbox (n N : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
    Aa n i * Aa n j * max (i^2 - j^2) 0
private def coneSum (n N : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc (0:ℤ) (N:ℤ), ∑ j ∈ Finset.Icc (-i) i,
    Aa n i * Aa n j * (i^2 - j^2)
end MetaMathlibExt
