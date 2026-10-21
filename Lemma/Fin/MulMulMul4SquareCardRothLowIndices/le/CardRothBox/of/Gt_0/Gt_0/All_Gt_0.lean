import Mathlib
import Lemma.Fin.Sum_SquareRothCenteredSum.le.DivMul_CardRothBox4.of.All_Gt_0
import Lemma.Fin.RothWeight.eq.AddRothCenteredSumDiv_2.of.RothBox
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[roth_low_indices_card_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {r : Fin m → ℕ}
  {γ : ℝ}
-- given
  (hr : ∀ h, 0 < r h)
  (hm : 0 < m)
  (hγ : 0 < γ) :
-- imply
  (4 : ℝ) * m * γ ^ 2 * (rothLowIndices r γ).card ≤
    Fintype.card (RothBox r) := by
-- proof
  let L := rothLowIndices r γ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpoint : ∀ j ∈ L, ((m : ℝ) * γ) ^ 2 ≤ rothCenteredSum r j ^ 2 := by
    intro j hj
    have hjlow := (Finset.mem_filter.mp hj).2
    rw [RothWeight.eq.AddRothCenteredSumDiv_2.of.RothBox] at hjlow
    have hs : rothCenteredSum r j < -((m : ℝ) * γ) := by linarith
    have hmg : 0 < (m : ℝ) * γ := mul_pos hmR hγ
    nlinarith
  have hlow :
    (L.card : ℝ) * ((m : ℝ) * γ) ^ 2 ≤
      ∑ j ∈ L, rothCenteredSum r j ^ 2 := calc
    _ = ∑ _ ∈ L, ((m : ℝ) * γ) ^ 2 := by simp
    _ ≤ ∑ j ∈ L, rothCenteredSum r j ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      apply hpoint j hj
  have hsubset :
    (∑ j ∈ L, rothCenteredSum r j ^ 2) ≤
      ∑ j : RothBox r, rothCenteredSum r j ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    ·
      apply Finset.filter_subset
    ·
      intro j _ _
      positivity
  have hmain :
    (L.card : ℝ) * ((m : ℝ) * γ) ^ 2 ≤
      (m : ℝ) * Fintype.card (RothBox r) / 4 :=
    hlow.trans (hsubset.trans (Sum_SquareRothCenteredSum.le.DivMul_CardRothBox4.of.All_Gt_0 hr))
  apply (mul_le_mul_iff_of_pos_left hmR).mp
  calc
    _ = 4 * ((L.card : ℝ) * ((m : ℝ) * γ) ^ 2) := by ring
    _ ≤ 4 * ((m : ℝ) * Fintype.card (RothBox r) / 4) := by
      gcongr
    _ = (m : ℝ) * Fintype.card (RothBox r) := by ring


-- created on 2026-10-21
