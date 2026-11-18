/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruence.lean -/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.PentagonalNumber
public import Theorem.Finset.Enumerative.PentagonalNumber
public import Theorem.Finset.Enumerative.GaussianBinomial
public import Def.Combinatorics.Enumerative.GaussianBinomial

@[expose] public section

/-!
# Ramanujan's partition congruences

Source: Hartosh Singh Bal and Gaurav Bhatnagar, "Glaisher's Divisors and
Infinite Products", Journal of Integer Sequences 27 (2024), Article 24.1.6,
proposition at lines 801–804.
Live TeX: https://cs.uwaterloo.ca/journals/JIS/VOL27/Bhatnagar/bhat4.tex

The source proposition is Ramanujan's partition congruence `p(5m + 4) ≡ 0`
(mod 5), where `p(n)` is the number of unordered integer partitions of `n`.
It holds also at `m = 0`, so quantifying over all `m : ℕ` is faithful.
It also proves the mod-7 congruence `p(7m + 5) ≡ 0` (mod 7), following
S. Ramanujan, "Some properties of p(n), the number of partitions of n",
Proceedings of the Cambridge Philosophical Society 19 (1919), 207–210.
-/


section

namespace MetaMathlibExt

open MathlibExt

/-- Jacobi's cube series in `ℤ⟦X⟧`, with `(-1) ^ t * (2 * t + 1)` at index
`(t + 1).choose 2` and `0` elsewhere. -/
noncomputable def jacobiCubeSeries : PowerSeries ℤ :=
  PowerSeries.mk fun b =>
    ∑ t ∈ Finset.range (b + 1),
      (if (t + 1).choose 2 = b then (-1 : ℤ) ^ t * (2 * t + 1) else 0)

noncomputable def finiteJacobiU (n : ℕ) :
    Polynomial (PowerSeries ℤ) :=
  ∏ i ∈ Finset.range n,
    ((1 - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1))
      * Polynomial.X)
      * (Polynomial.X
        - Polynomial.C ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1))))

noncomputable def finiteJacobiPoly (n : ℕ) :
    Polynomial (PowerSeries ℤ) :=
  (1 - Polynomial.X) * finiteJacobiU n

def jacobiExponent (n k : ℕ) : ℕ :=
  (n + 1 - k).choose 2 + (k - n).choose 2

noncomputable def jacobiCoeff (n k : ℕ) : PowerSeries ℤ :=
  (-1) ^ (n + k) * PowerSeries.X ^ (jacobiExponent n k)
    * gaussBinom (PowerSeries.X : PowerSeries ℤ) (2 * n + 1) k

end MetaMathlibExt
end
