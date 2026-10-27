import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
import Initialize.Tactic.Attr.Basic
open Set


@[path]
private lemma main
  {a b c m M : ℝ}
  (h₀ : 0 < a)
  (h₁ : m < M) :
-- imply
  sInf ((fun x => a * x ^ 2 + b * x + c) '' Icc m M) =
    if -b / (2 * a) ∈ Icc m M then c - b ^ 2 / (4 * a)
    else min (a * m ^ 2 + b * m + c) (a * M ^ 2 + b * M + c) := by
-- proof
  let f : ℝ → ℝ := fun x => a * x ^ 2 + b * x + c
  let v : ℝ := -b / (2 * a)
  let κ : ℝ := c - b ^ 2 / (4 * a)
  have ha : a ≠ 0 := ne_of_gt h₀
  have hsq (x : ℝ) : f x = a * (x - v) ^ 2 + κ := by
    unfold f v κ
    field_simp [ha]
    ring
  have hge (x : ℝ) : κ ≤ f x := by
    rw [hsq]
    have : 0 ≤ a * (x - v) ^ 2 := mul_nonneg h₀.le (sq_nonneg _)
    linarith
  if hv : v ∈ Icc m M then
    rw [ite_eq_left hv]
    have hleast : IsLeast (f '' Icc m M) κ := by
      constructor
      ·
        refine ⟨v, hv, ?_⟩
        rw [hsq]
        ring
      ·
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hy
        apply hge
    apply IsLeast.csInf_eq hleast
  else
    rw [ite_eq_right hv]
    have hsplit : v < m ∨ M < v := by
      rw [mem_Icc] at hv
      push Not at hv
      if hml : m ≤ v then
        right
        exact hv hml
      else
        left
        linarith
    if hvm : v < m then
      have hinc (x : ℝ) (hx : x ∈ Icc m M) : f m ≤ f x := by
        have hdiff : f x - f m = (x - m) * a * ((x - v) + (m - v)) := by
          rw [hsq, hsq]
          ring
        have hsum : 0 ≤ (x - v) + (m - v) := by linarith [hx.1]
        have hprod : 0 ≤ (x - m) * a * ((x - v) + (m - v)) := by
          apply mul_nonneg
          ·
            apply mul_nonneg
            · linarith [hx.1]
            · exact h₀.le
          · exact hsum
        linarith
      have hmin : min (f m) (f M) = f m := by
        apply min_eq_left
        apply hinc M
        constructor
        · linarith
        · exact le_rfl
      rw [hmin]
      have hleast : IsLeast (f '' Icc m M) (f m) := by
        constructor
        ·
          refine ⟨m, ?_, rfl⟩
          constructor
          · exact le_rfl
          · linarith
        ·
          intro y hy
          obtain ⟨x, hx, rfl⟩ := hy
          apply hinc x hx
      apply IsLeast.csInf_eq hleast
    else
      have hMv : M < v := by
        obtain (hlt | hgt) := hsplit
        · exact absurd hlt hvm
        · exact hgt
      have hdec (x : ℝ) (hx : x ∈ Icc m M) : f M ≤ f x := by
        have hdiff : f x - f M = (x - M) * a * ((x - v) + (M - v)) := by
          rw [hsq, hsq]
          ring
        have hsum : (x - v) + (M - v) ≤ 0 := by linarith [hx.2]
        have hprod : 0 ≤ (x - M) * a * ((x - v) + (M - v)) := by
          apply mul_nonneg_of_nonpos_of_nonpos
          ·
            apply mul_nonpos_of_nonpos_of_nonneg
            · linarith [hx.2]
            · exact h₀.le
          · exact hsum
        linarith
      have hmin : min (f m) (f M) = f M := by
        apply min_eq_right
        apply hdec m
        constructor
        · exact le_rfl
        · linarith
      rw [hmin]
      have hleast : IsLeast (f '' Icc m M) (f M) := by
        constructor
        ·
          refine ⟨M, ?_, rfl⟩
          constructor
          · linarith
          · exact le_rfl
        ·
          intro y hy
          obtain ⟨x, hx, rfl⟩ := hy
          apply hdec x hx
      apply IsLeast.csInf_eq hleast


-- created on 2021-10-02
-- updated on 2026-10-26
