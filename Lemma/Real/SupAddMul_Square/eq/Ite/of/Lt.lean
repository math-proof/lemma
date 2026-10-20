import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
import sympy.Basic
open Set


private lemma quadSup
  {a b c m M : ℝ}
  (h₀ : a < 0)
  (h₁ : m < M) :
-- imply
  sSup ((fun x => a * x ^ 2 + b * x + c) '' Icc m M) =
    if -b / (2 * a) ∈ Icc m M then c - b ^ 2 / (4 * a)
    else max (a * m ^ 2 + b * m + c) (a * M ^ 2 + b * M + c) := by
-- proof
  let f : ℝ → ℝ := fun x => a * x ^ 2 + b * x + c
  let v : ℝ := -b / (2 * a)
  let κ : ℝ := c - b ^ 2 / (4 * a)
  have ha : a ≠ 0 := ne_of_lt h₀
  have hsq (x : ℝ) : f x = a * (x - v) ^ 2 + κ := by
    unfold f v κ
    field_simp [ha]
    ring
  have hle (x : ℝ) : f x ≤ κ := by
    rw [hsq]
    have : a * (x - v) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h₀.le (sq_nonneg _)
    linarith
  if hv : v ∈ Icc m M then
    rw [ite_eq_left hv]
    have hgreat : IsGreatest (f '' Icc m M) κ := by
      constructor
      ·
        refine ⟨v, hv, ?_⟩
        rw [hsq]
        ring
      ·
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hy
        apply hle
    apply IsGreatest.csSup_eq hgreat
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
      have hdec (x : ℝ) (hx : x ∈ Icc m M) : f x ≤ f m := by
        have hdiff : f x - f m = (x - m) * a * ((x - v) + (m - v)) := by
          rw [hsq, hsq]
          ring
        have hsum : 0 ≤ (x - v) + (m - v) := by linarith [hx.1]
        have hprod : (x - m) * a * ((x - v) + (m - v)) ≤ 0 := by
          apply mul_nonpos_of_nonpos_of_nonneg
          ·
            apply mul_nonpos_of_nonneg_of_nonpos
            · linarith [hx.1]
            · exact h₀.le
          · exact hsum
        linarith
      have hmax : max (f m) (f M) = f m := by
        apply max_eq_left
        apply hdec M
        constructor
        · linarith
        · exact le_rfl
      rw [hmax]
      have hgreat : IsGreatest (f '' Icc m M) (f m) := by
        constructor
        ·
          refine ⟨m, ?_, rfl⟩
          constructor
          · exact le_rfl
          · linarith
        ·
          intro y hy
          obtain ⟨x, hx, rfl⟩ := hy
          apply hdec x hx
      apply IsGreatest.csSup_eq hgreat
    else
      have hMv : M < v := by
        obtain (hlt | hgt) := hsplit
        · exact absurd hlt hvm
        · exact hgt
      have hinc (x : ℝ) (hx : x ∈ Icc m M) : f x ≤ f M := by
        have hdiff : f M - f x = (M - x) * a * ((M - v) + (x - v)) := by
          rw [hsq, hsq]
          ring
        have hsum : (M - v) + (x - v) ≤ 0 := by linarith [hx.2]
        have hprod : 0 ≤ (M - x) * a * ((M - v) + (x - v)) := by
          apply mul_nonneg_of_nonpos_of_nonpos
          ·
            apply mul_nonpos_of_nonneg_of_nonpos
            · linarith [hx.2]
            · exact h₀.le
          · exact hsum
        linarith
      have hmax : max (f m) (f M) = f M := by
        apply max_eq_right
        apply hinc m
        constructor
        · exact le_rfl
        · linarith
      rw [hmax]
      have hgreat : IsGreatest (f '' Icc m M) (f M) := by
        constructor
        ·
          refine ⟨M, ?_, rfl⟩
          constructor
          · linarith
          · exact le_rfl
        ·
          intro y hy
          obtain ⟨x, hx, rfl⟩ := hy
          apply hinc x hx
      apply IsGreatest.csSup_eq hgreat


@[path]
private lemma main
  {a b c m M : ℝ}
  (h₀ : m < M) :
-- imply
  sSup ((fun x => a * x ^ 2 + b * x + c) '' Icc m M) =
    if -b / (2 * a) ∈ Icc m M ∧ a < 0 then c - b ^ 2 / (4 * a)
    else max (a * m ^ 2 + b * m + c) (a * M ^ 2 + b * M + c) := by
-- proof
  let f : ℝ → ℝ := fun x => a * x ^ 2 + b * x + c
  if ha : a < 0 then
    have hquad := quadSup (b := b) (c := c) ha h₀
    simpa [ha] using hquad
  else
    have ha0 : 0 ≤ a := le_of_not_gt ha
    rw [ite_eq_right (by intro h; exact ha h.2)]
    have hgreat : IsGreatest (f '' Icc m M) (max (f m) (f M)) := by
      constructor
      ·
        if hle : f m ≤ f M then
          rw [max_eq_right hle]
          refine ⟨M, ?_, rfl⟩
          constructor
          · linarith
          · exact le_rfl
        else
          rw [max_eq_left (le_of_not_ge hle)]
          refine ⟨m, ?_, rfl⟩
          constructor
          · exact le_rfl
          · linarith
      ·
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hy
        have hδ : 0 < M - m := sub_pos.2 h₀
        let t : ℝ := (x - m) / (M - m)
        have ht0 : 0 ≤ t := by
          unfold t
          apply div_nonneg
          · linarith [hx.1]
          · linarith
        have ht1 : t ≤ 1 := by
          unfold t
          rw [div_le_one hδ]
          linarith [hx.2]
        have hxlin : x = (1 - t) * m + t * M := by
          unfold t
          field_simp [hδ.ne']
          ring
        have hconv : (1 - t) * f m + t * f M - f x = a * t * (1 - t) * (M - m) ^ 2 := by
          rw [hxlin]
          unfold f
          ring
        have hnonneg : 0 ≤ (1 - t) * f m + t * f M - f x := by
          rw [hconv]
          apply mul_nonneg
          ·
            apply mul_nonneg
            · apply mul_nonneg ha0 ht0
            · linarith
          · exact sq_nonneg _
        have hcombo : (1 - t) * f m + t * f M ≤ max (f m) (f M) := by
          have hm : f m ≤ max (f m) (f M) := le_max_left _ _
          have hM : f M ≤ max (f m) (f M) := le_max_right _ _
          have h1 : (1 - t) * f m ≤ (1 - t) * max (f m) (f M) :=
            mul_le_mul_of_nonneg_left hm (by linarith)
          have h2 : t * f M ≤ t * max (f m) (f M) :=
            mul_le_mul_of_nonneg_left hM ht0
          have h3 : (1 - t) * max (f m) (f M) + t * max (f m) (f M) = max (f m) (f M) := by
            ring
          linarith
        linarith
    apply IsGreatest.csSup_eq hgreat


-- created on 2019-12-27
-- updated on 2026-10-17
