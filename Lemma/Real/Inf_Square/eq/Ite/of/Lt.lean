import Lemma.Real.Inf_Square.eq.Zero.of.Gt_0.Lt_0
import Lemma.Real.Inf_Square.eq.Square.of.Le_0.Lt
open Real


@[path]
private lemma main
  {m M : ℝ}
-- given
  (h₀ : m < M) :
-- imply
  sInf ((fun x => x ^ 2) '' Set.Ioo m M) =
    if m ≤ 0 ∧ 0 ≤ M then 0 else min (m ^ 2) (M ^ 2) := by
-- proof
  if hcross : m ≤ 0 ∧ 0 ≤ M then
    simp only [hcross]
    if hm : m < 0 then
      if hM : 0 < M then
        apply Inf_Square.eq.Zero.of.Gt_0.Lt_0 hM hm
      else
        have hM0 : M = 0 := le_antisymm (le_of_not_gt hM) hcross.2
        subst hM0
        simpa using Inf_Square.eq.Square.of.Le_0.Lt (m := m) (M := (0 : ℝ)) le_rfl h₀
    else
      have hm0 : m = 0 := le_antisymm hcross.1 (le_of_not_gt hm)
      subst hm0
      have hM : (0 : ℝ) < M := by linarith
      simpa using Inf_Square.eq.Square.of.Ge_0.Lt (m := (0 : ℝ)) (M := M) le_rfl hM
  else
    simp only [hcross]
    if hm : 0 < m then
      have hmin : min (m ^ 2) (M ^ 2) = m ^ 2 := by
        apply min_eq_left
        rw [sq_le_sq, abs_of_pos hm, abs_of_pos (lt_trans hm h₀)]
        linarith
      rw [hmin]
      simpa using Inf_Square.eq.Square.of.Ge_0.Lt (le_of_lt hm) h₀
    else
      have hM : M < 0 := by
        apply lt_of_not_ge
        intro h
        exact hcross ⟨le_of_not_gt hm, h⟩
      have hmin : min (m ^ 2) (M ^ 2) = M ^ 2 := by
        apply min_eq_right
        rw [sq_le_sq, abs_of_neg hM, abs_of_nonpos (le_of_not_gt hm)]
        linarith
      rw [hmin]
      simpa using Inf_Square.eq.Square.of.Le_0.Lt hM.le h₀


-- created on 2026-10-11
-- updated on 2026-10-17
