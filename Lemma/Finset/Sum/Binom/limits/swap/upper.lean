import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n h i : ℕ}
  (f : ℕ → ℝ) :
-- imply
  ∑ j ∈ Finset.Ico h n, ∑ k ∈ Finset.Ico j n, ((i + k - j).choose i : ℝ) * f k
    = ∑ k ∈ Finset.Ico h n, ((k + i + 1 - h).choose (i + 1) : ℝ) * f k := by
-- proof
  rw [Finset.sum_Ico_Ico_comm]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [← Finset.sum_mul]
  congr 1
  have hkh : h ≤ k := by
    simp only [Finset.mem_Ico] at hk
    exact hk.1
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : k + 1 - h = k - h + 1 := by omega
  rw [hlen]
  have hterm : ∀ t < (k - h + 1),
      ((i + k - (h + t)).choose i : ℝ) = ((i + ((k - h) - t)).choose i : ℝ) := by
    intro t ht
    have hle : h + t ≤ k := by omega
    rw [Nat.add_sub_assoc hle, Nat.sub_add_eq]
  have hcong : ∑ t < (k - h + 1), ((i + k - (h + t)).choose i : ℝ) =
    ∑ t < (k - h + 1), ((i + ((k - h) - t)).choose i : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    exact hterm t (by simpa using ht)
  simp only [Nat.Iio_eq_range] at hcong
  rw [hcong]
  have href := Finset.sum_range_reflect (fun s => ((i + s).choose i : ℝ)) (k - h + 1)
  have : ∑ t < (k - h + 1), ((i + ((k - h) - t)).choose i : ℝ) =
    ∑ t < (k - h + 1), ((i + t).choose i : ℝ) := by
    simp only [Nat.Iio_eq_range]
    simpa using href
  simp only [Nat.Iio_eq_range] at this
  rw [this]
  have hs := Nat.sum_range_add_choose (k - h) i
  have hcast := congrArg (Nat.cast : ℕ → ℝ) hs
  have hidx : k - h + i + 1 = k + i + 1 - h := by omega
  simp only [add_comm i]
  rw [Nat.add_comm 1 i]
  simpa [hidx] using hcast


-- created on 2023-06-03
-- updated on 2026-10-26
