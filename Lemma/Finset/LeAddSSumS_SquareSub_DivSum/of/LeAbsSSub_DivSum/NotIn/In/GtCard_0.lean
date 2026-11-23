import Instance.Data.Fin.Fun
import Instance.Data.Nat.Fun
import Notation.Algebra.Power
import Lemma.Finset.Sum_SquareSub_DivSum.eq.Sub_DivSquareSum
open Finset


/--
A step used in k-means / clustering convergence: if a point `y'` is at least as
close to the mean of cluster `X` as to the mean of cluster `Y`, then moving `y'`
from `Y` into `X` does not increase the total within-cluster sum of squared
errors (SSE). Thus reassignment toward nearer centroids is monotone in the
k-means objective and supports convergence arguments.
-/
@[path]
private lemma main
  [DecidableEq α]
  {y' : α}
  {X Y : Finset α}
  {a : α → ℝ}
-- given
  (h₀ : X.card > 0)
  (h₁ : y' ∈ Y)
  (h₂ : y' ∉ X)
  (h₃ : |a y' - (∑ x ∈ X, a x) / X.card| ≤ |a y' - (∑ y ∈ Y, a y) / Y.card|) :
-- imply
  (∑ x ∈ X ∪ {y'}, (a x - (∑ x ∈ X ∪ {y'}, a x) / ((X.card + 1 : ℕ) : ℝ))²) +
      ∑ y ∈ Y \ {y'}, (a y - (∑ y ∈ Y \ {y'}, a y) / ((Y.card - 1 : ℕ) : ℝ))² ≤
    (∑ x ∈ X, (a x - (∑ x ∈ X, a x) / X.card)²) +
      ∑ y ∈ Y, (a y - (∑ y ∈ Y, a y) / Y.card)² := by
-- proof
  if hm : Y.card = 1 then
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hm
    have hY : Y = {y'} := by
      rw [hy]
      rw [hy, Finset.mem_singleton] at h₁
      rw [h₁]
    have hmean : (∑ y ∈ Y, a y) / Y.card = a y' := by
      simp [hY]
    have heq : a y' = (∑ x ∈ X, a x) / X.card := by
      rw [hmean] at h₃
      apply sub_eq_zero.mp (abs_eq_zero.mp _)
      apply le_antisymm
      · simpa using h₃
      · apply abs_nonneg
    have hsum : ∑ x ∈ X ∪ {y'}, a x = (∑ x ∈ X, a x) + a y' := by
      simpa [Finset.union_singleton, add_comm] using Finset.sum_insert (f := a) h₂
    have hmeanI : (∑ x ∈ X ∪ {y'}, a x) / ((X.card + 1 : ℕ) : ℝ) = a y' := by
      rw [hsum, heq]
      field_simp
      rw [Nat.cast_add, Nat.cast_one]
    simp_rw [hY, Finset.union_singleton, Finset.sdiff_singleton_eq_erase] at hmeanI ⊢
    rw [Finset.sum_insert h₂, hmeanI, heq]
    simp [Finset.erase_singleton]
  else
    have hge : 2 ≤ Y.card := by
      have hpos : 0 < Y.card := Finset.card_pos.mpr ⟨y', h₁⟩
      omega
    set n : ℕ := X.card
    set m : ℕ := Y.card
    set S : ℝ := ∑ x ∈ X, a x
    set T : ℝ := ∑ y ∈ Y, a y
    set yv : ℝ := a y'
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h₀.ne'
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hcardI : (X ∪ {y'}).card = n + 1 := by
      rw [Finset.union_singleton]
      apply Finset.card_insert_of_notMem h₂
    have hsumI : ∑ x ∈ X ∪ {y'}, a x = S + yv := by
      simpa [Finset.union_singleton, S, yv, add_comm] using Finset.sum_insert (f := a) h₂
    have hsumE : ∑ y ∈ Y \ {y'}, a y = T - yv := by
      simpa [Finset.sdiff_singleton_eq_erase, T, yv] using
        eq_sub_of_add_eq (Finset.sum_erase_add Y a h₁)
    have hsqI : ∑ x ∈ X ∪ {y'}, (a x)² = (∑ x ∈ X, (a x)²) + yv² := by
      simpa [Finset.union_singleton, yv, add_comm] using
        Finset.sum_insert (f := fun x => (a x)²) h₂
    have hsqE : ∑ y ∈ Y \ {y'}, (a y)² = (∑ y ∈ Y, (a y)²) - yv² := by
      simpa [Finset.sdiff_singleton_eq_erase, yv] using
        eq_sub_of_add_eq (Finset.sum_erase_add Y (fun y => (a y)²) h₁)
    have hIX : ∑ x ∈ X ∪ {y'}, (a x - (∑ x ∈ X ∪ {y'}, a x) / ((n + 1 : ℕ) : ℝ))² =
        (∑ x ∈ X, (a x)²) + yv² - (S + yv)² / ((n : ℝ) + 1) := by
      have hden : ((X ∪ {y'}).card : ℝ) = (n : ℝ) + 1 := by
        rw [hcardI, Nat.cast_add, Nat.cast_one]
      rw [← hcardI, Sum_SquareSub_DivSum.eq.Sub_DivSquareSum.fun, hsqI, hsumI, hden]
    have hEY : ∑ y ∈ Y \ {y'}, (a y - (∑ y ∈ Y \ {y'}, a y) / ((m - 1 : ℕ) : ℝ))² =
        (∑ y ∈ Y, (a y)²) - yv² - (T - yv)² / ((m : ℝ) - 1) := by
      simp_rw [Finset.sdiff_singleton_eq_erase] at hsqE hsumE ⊢
      have hden : ((Y.erase y').card : ℝ) = (m : ℝ) - 1 := by
        rw [Finset.card_erase_of_mem h₁, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
      rw [← Finset.card_erase_of_mem h₁, Sum_SquareSub_DivSum.eq.Sub_DivSquareSum.fun, hsqE, hsumE, hden]
    have hX : ∑ x ∈ X, (a x - S / n)² = (∑ x ∈ X, (a x)²) - S² / n := by
      simpa [S, n] using Sum_SquareSub_DivSum.eq.Sub_DivSquareSum.fun
    have hY : ∑ y ∈ Y, (a y - T / m)² = (∑ y ∈ Y, (a y)²) - T² / m := by
      simpa [T, m] using Sum_SquareSub_DivSum.eq.Sub_DivSquareSum.fun
    have hgoal :
      ((∑ x ∈ X, (a x)²) + yv² - (S + yv)² / ((n : ℝ) + 1) +
        ((∑ y ∈ Y, (a y)²) - yv² - (T - yv)² / ((m : ℝ) - 1))) -
        (((∑ x ∈ X, (a x)²) - S² / n) + ((∑ y ∈ Y, (a y)²) - T² / m)) =
        (n : ℝ) / ((n : ℝ) + 1) * (yv - S / n)² -
          (m : ℝ) / ((m : ℝ) - 1) * (yv - T / m)² := by
      have hn1 : (n : ℝ) + 1 ≠ 0 := by
        rw [← Nat.cast_one, ← Nat.cast_add]
        apply Nat.cast_ne_zero.mpr
        omega
      have hmm : (m : ℝ) - 1 ≠ 0 := by
        rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ m)]
        apply Nat.cast_ne_zero.mpr
        omega
      field_simp [hn0, hn1, hm0, hmm]
      ring
    have hle : (n : ℝ) / ((n : ℝ) + 1) * (yv - S / n)² ≤
        (m : ℝ) / ((m : ℝ) - 1) * (yv - T / m)² := by
      have hd : (yv - S / n)² ≤ (yv - T / m)² := by
        have habs : |yv - S / n| ≤ |yv - T / m| := by simpa [yv, S, T, n, m] using h₃
        have hsq : |yv - S / n|² ≤ |yv - T / m|² := by gcongr
        simpa [sq_abs] using hsq
      have hposX : 0 ≤ (yv - S / n)² := sq_nonneg _
      have hfracX : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by linarith : 0 < (n : ℝ) + 1)]
        linarith
      have hmpos : 0 < (m : ℝ) - 1 := by
        have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hge
        linarith
      have hfracY : 1 ≤ (m : ℝ) / ((m : ℝ) - 1) := by
        rw [one_le_div hmpos]
        linarith
      have h1 : (n : ℝ) / ((n : ℝ) + 1) * (yv - S / n)² ≤ (yv - S / n)² :=
        mul_le_of_le_one_left hposX hfracX
      have h2 : (yv - T / m)² ≤ (m : ℝ) / ((m : ℝ) - 1) * (yv - T / m)² := by
        have hnn : 0 ≤ (yv - T / m)² := sq_nonneg _
        simpa [one_mul] using mul_le_mul_of_nonneg_right hfracY hnn
      linarith
    rw [hIX, hEY, hX, hY]
    linarith [hgoal, hle]


-- created on 2021-03-25
-- updated on 2026-11-20
