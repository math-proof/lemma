/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SetPartitionsByTwoRises.lean -/

import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic.Ring

section
open scoped BigOperators

namespace MetaMathlibExt

/-- The auxiliary series `q = 1 - x + x * y` appearing in the denominator factors. -/
private noncomputable def qSeries : MvPowerSeries (Fin 2) ℚ :=
  (1 : MvPowerSeries (Fin 2) ℚ) - MvPowerSeries.X 0 +
    MvPowerSeries.X 0 * MvPowerSeries.X 1

/-- The denominator factors `D_j = q ^ j - y`. -/
private noncomputable def dSeries (j : ℕ) : MvPowerSeries (Fin 2) ℚ :=
  qSeries ^ j - MvPowerSeries.X 1

/-- The right-hand side of the main theorem, as a function of `k`. -/
private noncomputable def tSeries (k : ℕ) : MvPowerSeries (Fin 2) ℚ :=
  let x : MvPowerSeries (Fin 2) ℚ := MvPowerSeries.X 0
  let y : MvPowerSeries (Fin 2) ℚ := MvPowerSeries.X 1
  x ^ k * y ^ (k - 1) * (1 - y) ^ k *
    (∏ j ∈ Finset.Icc 1 k, (qSeries ^ j - y))⁻¹

-- Core counting definitions matching the main theorem predicate.
private def IsRGF (N k : ℕ) (π : Fin N → Fin k) : Prop :=
  Function.Surjective π ∧
    ∀ i : Fin N,
      (π i).val ≤
        ((Finset.univ.filter fun j : Fin N => j < i).image π).card

private def risesCount (N k : ℕ) (π : Fin N → Fin k) : ℕ :=
  (Finset.univ.filter fun p : Fin N × Fin N =>
    p.2.val = p.1.val + 1 ∧ π p.1 < π p.2).card

private def countRGF (N r k : ℕ) : ℕ :=
  Fintype.card
    {π : Fin N → Fin k //
      Function.Surjective π ∧
        (∀ i : Fin N,
          (π i).val ≤
            ((Finset.univ.filter fun j : Fin N => j < i).image π).card) ∧
        risesCount N k π = r}

private noncomputable def aSeries (k : ℕ) : MvPowerSeries (Fin 2) ℚ :=
  fun d => (countRGF (d 0) (d 1) k : ℚ)

private def countLast (n r k : ℕ) (c : Fin k) : ℕ :=
  Fintype.card
    {π : Fin (n + 1) → Fin k //
      Function.Surjective π ∧
        (∀ i : Fin (n + 1),
          (π i).val ≤
            ((Finset.univ.filter fun j : Fin (n + 1) => j < i).image π).card) ∧
        risesCount (n + 1) k π = r ∧ π (Fin.last n) = c}

private noncomputable def bSeries (k : ℕ) (c : Fin k) :
    MvPowerSeries (Fin 2) ℚ :=
  fun d => if d 0 = 0 then 0 else (countLast (d 0 - 1) (d 1) k c : ℚ)
end MetaMathlibExt
end
