import sympy.Basic


@[path]
private lemma main
  {ε r A : ℝ}
  (h₀ : 0 < ε)
  (h₁ : ε < 1) :
-- imply
  min (r * A) (max (1 - ε) (min (1 + ε) r) * A) =
    if 0 ≤ A then A * min r (1 + ε) else A * max r (1 - ε) := by
-- proof
  have hlohi : 1 - ε ≤ 1 + ε := by linarith
  if hA : 0 ≤ A then
    if hr : 1 + ε ≤ r then
      have hclip : max (1 - ε) (min (1 + ε) r) = 1 + ε := by
        rw [min_eq_left hr, max_eq_right hlohi]
      rw [ite_eq_left hA, hclip, min_eq_right hr]
      rw [min_eq_right (by nlinarith : (1 + ε) * A ≤ r * A)]
      ring
    else
      if hr' : r ≤ 1 - ε then
        have hrm : r ≤ 1 + ε := by linarith
        have hclip : max (1 - ε) (min (1 + ε) r) = 1 - ε := by
          rw [min_eq_right hrm, max_eq_left hr']
        rw [ite_eq_left hA, hclip, min_eq_left hrm]
        rw [min_eq_left (by nlinarith : r * A ≤ (1 - ε) * A)]
        ring
      else
        have hmidl : 1 - ε ≤ r := by linarith
        have hmidr : r ≤ 1 + ε := by linarith
        have hclip : max (1 - ε) (min (1 + ε) r) = r := by
          rw [min_eq_right hmidr, max_eq_right hmidl]
        rw [ite_eq_left hA, hclip, min_eq_left hmidr, min_self]
        ring
  else
    if hr : 1 + ε ≤ r then
      have hclip : max (1 - ε) (min (1 + ε) r) = 1 + ε := by
        rw [min_eq_left hr, max_eq_right hlohi]
      rw [ite_eq_right hA, hclip, max_eq_left (by linarith : 1 - ε ≤ r)]
      rw [min_eq_left (by nlinarith : r * A ≤ (1 + ε) * A)]
      ring
    else
      if hr' : r ≤ 1 - ε then
        have hrm : r ≤ 1 + ε := by linarith
        have hclip : max (1 - ε) (min (1 + ε) r) = 1 - ε := by
          rw [min_eq_right hrm, max_eq_left hr']
        rw [ite_eq_right hA, hclip, max_eq_right hr']
        rw [min_eq_right (by nlinarith : (1 - ε) * A ≤ r * A)]
        ring
      else
        have hmidl : 1 - ε ≤ r := by linarith
        have hmidr : r ≤ 1 + ε := by linarith
        have hclip : max (1 - ε) (min (1 + ε) r) = r := by
          rw [min_eq_right hmidr, max_eq_right hmidl]
        rw [ite_eq_right hA, hclip, max_eq_left hmidl, min_self]
        ring


-- created on 2026-10-11
-- updated on 2026-10-17
