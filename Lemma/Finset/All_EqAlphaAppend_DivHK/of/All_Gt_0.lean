import sympy.concrete.continued_fraction
import sympy.Basic
import Lemma.Finset.AlphaAppend.eq.AlphaAppend_AddDiv
import Lemma.Finset.All_GeK_0.et.GtK_Add_1_0.of.All_Gt_0
open Finset Continuant


@[path]
private lemma main
-- given
  (x : ℕ → ℝ)
  (h : ∀ i, 0 < x i)
  (n : ℕ) :
-- imply
  ∀ {t : ℝ}, 0 < t → alpha ((List.range (n + 1)).map x ++ [t]) =
      (H x (n + 1) * t + H x n) / (K x (n + 1) * t + K x n) := by
-- proof
  induction n with
  | zero =>
    intro t ht
    have ht' := ht.ne'
    simp [alpha, H, K]
    field_simp
  | succ n ih =>
    intro t ht
    have hx := h (n + 1)
    have e : (List.range (n + 1 + 1)).map x ++ [t] = (List.range (n + 1)).map x ++ [x (n + 1), t] := by
      rw [List.range_succ (n := n + 1), List.map_append, List.append_assoc]
      rfl
    rw [e, AlphaAppend.eq.AlphaAppend_AddDiv, ih (add_pos hx (one_div_pos.mpr ht))]
    have k := All_GeK_0.et.GtK_Add_1_0.of.All_Gt_0 x h n
    have k' := All_GeK_0.et.GtK_Add_1_0.of.All_Gt_0 x h (n + 1)
    have hd1 : K x (n + 1) * (x (n + 1) + 1 / t) + K x n ≠ 0 :=
      (add_pos_of_pos_of_nonneg (mul_pos k.2 (add_pos hx (one_div_pos.mpr ht))) k.1).ne'
    have hd2 : K x (n + 1 + 1) * t + K x (n + 1) ≠ 0 :=
      (add_pos_of_pos_of_nonneg (mul_pos k'.2 ht) k'.1).ne'
    rw [div_eq_div_iff hd1 hd2]
    show (H x (n + 1) * (x (n + 1) + 1 / t) + H x n) * ((K x (n + 1) * x (n + 1) + K x n) * t + K x (n + 1)) =
      ((H x (n + 1) * x (n + 1) + H x n) * t + H x (n + 1)) * (K x (n + 1) * (x (n + 1) + 1 / t) + K x n)
    have ht' := ht.ne'
    field_simp
    ring


-- created on 2026-10-07
