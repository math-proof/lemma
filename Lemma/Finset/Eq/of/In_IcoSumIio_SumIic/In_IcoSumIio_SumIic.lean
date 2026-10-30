import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin
import Notation.Fun
import Syntax.Fun
import Initialize.Tactic.Attr.Basic


/--
Each position belongs to at most one block of a partition of `Fin n`.
-/
@[path]
private lemma main
  {n : ℕ}
  {d : Fin n ⇀ ℕ}
  {t : ℕ}
  {k₁ k₂ : Fin n}
-- given
  (hk₁ : t ∈ Finset.Ico (∑ j ∈ Finset.Iio k₁, d[j]) (∑ j ∈ Finset.Iic k₁, d[j]))
  (hk₂ : t ∈ Finset.Ico (∑ j ∈ Finset.Iio k₂, d[j]) (∑ j ∈ Finset.Iic k₂, d[j])) :
-- imply
  k₁ = k₂ := by
-- proof
  by_contra hne
  obtain hlt | hlt := lt_or_gt_of_ne hne
  ·
    have hsub : Finset.Iic k₁ ⊆ Finset.Iio k₂ := by
      intro j hj
      rw [Finset.mem_Iic, Fin.le_def] at hj
      rw [Finset.mem_Iio, Fin.lt_def]
      exact Nat.lt_of_le_of_lt hj (Fin.lt_def.mp hlt)
    have hle : ∑ j ∈ Finset.Iic k₁, d[j] ≤ ∑ j ∈ Finset.Iio k₂, d[j] :=
      Finset.sum_le_sum_of_subset hsub
    simp only [Finset.mem_Ico] at hk₁ hk₂
    omega
  ·
    have hsub : Finset.Iic k₂ ⊆ Finset.Iio k₁ := by
      intro j hj
      rw [Finset.mem_Iic, Fin.le_def] at hj
      rw [Finset.mem_Iio, Fin.lt_def]
      exact Nat.lt_of_le_of_lt hj (Fin.lt_def.mp hlt)
    have hle : ∑ j ∈ Finset.Iic k₂, d[j] ≤ ∑ j ∈ Finset.Iio k₁, d[j] :=
      Finset.sum_le_sum_of_subset hsub
    simp only [Finset.mem_Ico] at hk₁ hk₂
    omega


-- created on 2026-10-25
