import Lemma.Finset.LeAddSumS_SquareSub_Div_Sum.of.LeAbsSSub_Div_Sum.NotIn.In.GtCard_0
import Lemma.Finset.Sum_SquareSub_DivSum.eq.Sub_DivSquareSum
open Finset


/--
Strict sibling of the k-means SSE reassignment lemma: if `y'` is *strictly*
closer to the mean of cluster `X` than to the mean of cluster `Y`, then moving
`y'` from `Y` into `X` *strictly* decreases the total within-cluster sum of
squared errors. Proved from the non-strict `Le` form plus the algebraic
identity that the SSE drop equals a positive combination of the squared mean
deviations under a strict Abs hypothesis.
-/
@[path]
private lemma main
  [DecidableEq α]
  {y' : α}
  {X Y : Finset α}
  {a : α ⇀ ℝ}
-- given
  (h₀ : X.card > 0)
  (h₁ : y' ∈ Y)
  (h₂ : y' ∉ X)
  (h₃ : |a[y'] - (∑ x ∈ X, a[x]) / (X.card : ℝ)| < |a[y'] - (∑ y ∈ Y, a[y]) / (Y.card : ℝ)|) :
-- imply
  (∑ x ∈ X ∪ {y'}, (a[x] - (∑ x ∈ X ∪ {y'}, a[x]) / ((X.card + 1 : ℕ) : ℝ)) ^ 2) +
      ∑ y ∈ Y \ {y'}, (a[y] - (∑ y ∈ Y \ {y'}, a[y]) / ((Y.card - 1 : ℕ) : ℝ)) ^ 2 <
    (∑ x ∈ X, (a[x] - (∑ x ∈ X, a[x]) / (X.card : ℝ)) ^ 2) +
      ∑ y ∈ Y, (a[y] - (∑ y ∈ Y, a[y]) / (Y.card : ℝ)) ^ 2 := by
-- proof
  apply lt_of_le_of_ne
    (LeAddSumS_SquareSub_Div_Sum.of.LeAbsSSub_Div_Sum.NotIn.In.GtCard_0 h₀ h₁ h₂ (le_of_lt h₃))
  intro heq
  have hge : 2 ≤ Y.card := by
    have hne1 : Y.card ≠ 1 := by
      intro hm
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hm
      have hyz : y' = y := by
        have hym : y' ∈ Y := h₁
        rwa [hy, Finset.mem_singleton] at hym
      have hY : Y = {y'} := by
        rw [hy, hyz]
      have hmean : (∑ y ∈ Y, a[y]) / (Y.card : ℝ) = a[y'] := by
        simp [hY]
      have habs := h₃
      rw [hmean] at habs
      have : |a[y'] - (∑ x ∈ X, a[x]) / (X.card : ℝ)| < 0 := by simpa using habs
      exact (not_lt_of_ge (abs_nonneg _)) this
    have hpos : 0 < Y.card := Finset.card_pos.mpr ⟨y', h₁⟩
    omega
  set n : ℕ := X.card
  set m : ℕ := Y.card
  set S : ℝ := ∑ x ∈ X, a[x]
  set T : ℝ := ∑ y ∈ Y, a[y]
  set yv : ℝ := a[y']
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h₀.ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hcardI : (X ∪ {y'}).card = n + 1 := by
    rw [Finset.union_singleton]; exact Finset.card_insert_of_notMem h₂
  have hsumI : ∑ x ∈ X ∪ {y'}, a[x] = S + yv := by
    simpa [Finset.union_singleton, S, yv, add_comm] using Finset.sum_insert (f := a) h₂
  have hsumE : ∑ y ∈ Y \ {y'}, a[y] = T - yv := by
    simpa [Finset.sdiff_singleton_eq_erase, T, yv] using
      eq_sub_of_add_eq (Finset.sum_erase_add Y a h₁)
  have hsqI : ∑ x ∈ X ∪ {y'}, a[x] ^ 2 = (∑ x ∈ X, a[x] ^ 2) + yv ^ 2 := by
    simpa [Finset.union_singleton, yv, add_comm] using
      Finset.sum_insert (f := fun x => a[x] ^ 2) h₂
  have hsqE : ∑ y ∈ Y \ {y'}, a[y] ^ 2 = (∑ y ∈ Y, a[y] ^ 2) - yv ^ 2 := by
    simpa [Finset.sdiff_singleton_eq_erase, yv] using
      eq_sub_of_add_eq (Finset.sum_erase_add Y (fun y => a[y] ^ 2) h₁)
  have hIX : ∑ x ∈ X ∪ {y'}, (a[x] - (∑ x ∈ X ∪ {y'}, a[x]) / ((n + 1 : ℕ) : ℝ)) ^ 2 =
      (∑ x ∈ X, a[x] ^ 2) + yv ^ 2 - (S + yv) ^ 2 / ((n : ℝ) + 1) := by
    have hden : ((X ∪ {y'}).card : ℝ) = (n : ℝ) + 1 := by
      rw [hcardI, Nat.cast_add, Nat.cast_one]
    rw [← hcardI, Sum_SquareSub_DivSum.eq.Sub_DivSquareSum.fun, hsqI, hsumI, hden]
  have hEY : ∑ y ∈ Y \ {y'}, (a[y] - (∑ y ∈ Y \ {y'}, a[y]) / ((m - 1 : ℕ) : ℝ)) ^ 2 =
      (∑ y ∈ Y, a[y] ^ 2) - yv ^ 2 - (T - yv) ^ 2 / ((m : ℝ) - 1) := by
    simp_rw [Finset.sdiff_singleton_eq_erase] at hsqE hsumE ⊢
    have hden : ((Y.erase y').card : ℝ) = (m : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem h₁, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    rw [← Finset.card_erase_of_mem h₁, Sum_SquareSub_DivSum.eq.Sub_DivSquareSum.fun, hsqE, hsumE, hden]
  have hX : ∑ x ∈ X, (a[x] - S / (n : ℝ)) ^ 2 = (∑ x ∈ X, a[x] ^ 2) - S ^ 2 / (n : ℝ) := by
    simpa [S, n] using Sum_SquareSub_DivSum.eq.Sub_DivSquareSum.fun
  have hY : ∑ y ∈ Y, (a[y] - T / (m : ℝ)) ^ 2 = (∑ y ∈ Y, a[y] ^ 2) - T ^ 2 / (m : ℝ) := by
    simpa [T, m] using Sum_SquareSub_DivSum.eq.Sub_DivSquareSum.fun
  have hgoal :
    ((∑ x ∈ X, a[x] ^ 2) + yv ^ 2 - (S + yv) ^ 2 / ((n : ℝ) + 1) +
      ((∑ y ∈ Y, a[y] ^ 2) - yv ^ 2 - (T - yv) ^ 2 / ((m : ℝ) - 1))) -
      (((∑ x ∈ X, a[x] ^ 2) - S ^ 2 / (n : ℝ)) + ((∑ y ∈ Y, a[y] ^ 2) - T ^ 2 / (m : ℝ))) =
      (n : ℝ) / ((n : ℝ) + 1) * (yv - S / (n : ℝ)) ^ 2 -
        (m : ℝ) / ((m : ℝ) - 1) * (yv - T / (m : ℝ)) ^ 2 := by
    have hn1 : (n : ℝ) + 1 ≠ 0 := by
      rw [← Nat.cast_one, ← Nat.cast_add]
      exact Nat.cast_ne_zero.mpr (by omega)
    have hmm : (m : ℝ) - 1 ≠ 0 := by
      rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ m)]
      exact Nat.cast_ne_zero.mpr (by omega)
    field_simp [hn0, hn1, hm0, hmm]
    ring
  have hd : (yv - S / (n : ℝ)) ^ 2 < (yv - T / (m : ℝ)) ^ 2 := by
    have habs : |yv - S / (n : ℝ)| < |yv - T / (m : ℝ)| := by simpa [yv, S, T, n, m] using h₃
    have hsq : |yv - S / (n : ℝ)| ^ 2 < |yv - T / (m : ℝ)| ^ 2 := by
      exact (sq_lt_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr habs
    simpa [sq_abs] using hsq
  have hposX : 0 ≤ (yv - S / (n : ℝ)) ^ 2 := sq_nonneg _
  have hfracX : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by linarith : 0 < (n : ℝ) + 1)]
    linarith
  have hmpos : 0 < (m : ℝ) - 1 := by
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hge
    linarith
  have hfracY : 1 ≤ (m : ℝ) / ((m : ℝ) - 1) := by
    rw [one_le_div hmpos]
    linarith
  have h1 : (n : ℝ) / ((n : ℝ) + 1) * (yv - S / (n : ℝ)) ^ 2 ≤ (yv - S / (n : ℝ)) ^ 2 :=
    mul_le_of_le_one_left hposX hfracX
  have h2 : (yv - T / (m : ℝ)) ^ 2 ≤ (m : ℝ) / ((m : ℝ) - 1) * (yv - T / (m : ℝ)) ^ 2 := by
    have hnn : 0 ≤ (yv - T / (m : ℝ)) ^ 2 := sq_nonneg _
    simpa [one_mul] using mul_le_mul_of_nonneg_right hfracY hnn
  have hlt :
    (n : ℝ) / ((n : ℝ) + 1) * (yv - S / (n : ℝ)) ^ 2 <
      (m : ℝ) / ((m : ℝ) - 1) * (yv - T / (m : ℝ)) ^ 2 := by
    linarith [h1, hd, h2]
  have hdiff :
    ((∑ x ∈ X, a[x] ^ 2) + yv ^ 2 - (S + yv) ^ 2 / ((n : ℝ) + 1) +
      ((∑ y ∈ Y, a[y] ^ 2) - yv ^ 2 - (T - yv) ^ 2 / ((m : ℝ) - 1))) -
      (((∑ x ∈ X, a[x] ^ 2) - S ^ 2 / (n : ℝ)) + ((∑ y ∈ Y, a[y] ^ 2) - T ^ 2 / (m : ℝ))) < 0 := by
    linarith [hgoal, hlt]
  rw [hIX, hEY, hX, hY] at heq
  linarith [hdiff, heq]


-- created on 2026-10-31
