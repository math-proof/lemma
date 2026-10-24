/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SetPartitionPeaks.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open scoped BigOperators
private def tpRgf (n k : ℕ) : Finset (Fin n → Fin k) :=
  Finset.univ.filter fun f : Fin n → Fin k =>
    Function.Surjective f ∧
    ∀ i : Fin n, ∀ m : Fin k,
      m.val < (f i).val → ∃ j : Fin n, j.val < i.val ∧ f j = m

private def tpH (n k j : ℕ) : ℕ := ∑ t ∈ Finset.range n, j ^ t * Nat.stirlingSecond (n - 1 - t) k

private def tpSq (K : ℕ) : ℕ := ∑ b ∈ Finset.range K, b * b

private def tpPeaks (n K : ℕ) (f : Fin n → Fin K) : ℕ :=
  (Finset.univ.filter (fun i : Fin n =>
    i.val ≠ 0 ∧
    if h : i.val + 1 < n then
      (f ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩).val <
          (f i).val ∧
        (f ⟨i.val + 1, h⟩).val < (f i).val
    else False)).card

private def tpT (n k : ℕ) : ℕ := ∑ f ∈ tpRgf n k, tpPeaks n k f

private def tpR (n k : ℕ) : ℕ :=
  Nat.choose k 2 * Nat.stirlingSecond (n - 1) k +
    ∑ j ∈ Finset.Icc 2 k,
      (j * Nat.choose j 2 - Nat.choose (j + 1) 3) *
        ∑ i ∈ Finset.Icc 3 (n - k),
          j ^ (i - 3) * Nat.stirlingSecond (n - i) k

private def tpA (n k : ℕ) : ℕ :=
  ∑ g ∈ tpRgf (n+2) (k+1),
    (if (g (Fin.castSucc (Fin.last n))).val < (g (Fin.last (n+1))).val
      then (g (Fin.last (n+1))).val else 0)

private def tpPk (m K : ℕ) (f : Fin m → Fin K) (v : ℕ) : ℕ :=
  if h : v < m then
    if _ : 0 < v then
      if hv1 : v + 1 < m then
        if (f ⟨v - 1, lt_of_le_of_lt (Nat.sub_le v 1) h⟩).val < (f ⟨v, h⟩).val ∧
           (f ⟨v + 1, hv1⟩).val < (f ⟨v, h⟩).val then 1 else 0
      else 0
    else 0
  else 0
section
namespace MetaMathlibExt
end MetaMathlibExt
end
