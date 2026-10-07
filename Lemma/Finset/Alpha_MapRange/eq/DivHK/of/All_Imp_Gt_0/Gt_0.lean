import sympy.Basic
import Lemma.Finset.Alpha_Cons.eq.Add_DivAlpha
import Lemma.Finset.All_GeK_0.et.GtK_Add_1_0.of.All_Gt_0
import Lemma.Finset.Alpha_MapRange.eq.DivHK.of.All_Gt_0
import Lemma.Finset.All_Imp_EqK_EqH.of.All_Imp_Eq
open Finset Continuant


@[main]
private lemma main
  {n : ℕ}
-- given
  (x : ℕ → ℝ)
  (hn : 0 < n)
  (h : ∀ j, 1 ≤ j → j < n → 0 < x j) :
-- imply
  alpha ((List.range n).map x) = H x n / K x n := by
-- proof
  let y : ℕ → ℝ := fun j => if 1 ≤ j ∧ j < n then x j else 1
  have hy : ∀ j, 0 < y j := by
    intro j
    if hj : 1 ≤ j ∧ j < n then
      simp only [y, if_pos hj]
      exact h j hj.1 hj.2
    else
      simp only [y, if_neg hj]
      exact one_pos
  have hxy : ∀ j, 1 ≤ j → j < n → x j = y j := by
    intro j h1 h2
    simp only [y, if_pos (And.intro h1 h2)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have key := (All_Imp_EqK_EqH.of.All_Imp_Eq x y (m + 1) hxy m le_rfl).2
  have hK := (All_GeK_0.et.GtK_Add_1_0.of.All_Gt_0 y hy m).2
  have ha := Alpha_MapRange.eq.DivHK.of.All_Gt_0 y hy m
  rw [key.1, key.2]
  have hl : alpha ((List.range (m + 1)).map x) = alpha ((List.range (m + 1)).map y) + (x 0 - y 0) := by
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
    cases m with
    | zero =>
      simp [alpha]
    | succ k =>
      rw [Alpha_Cons.eq.Add_DivAlpha _ (by simp), Alpha_Cons.eq.Add_DivAlpha _ (by simp)]
      have e : List.map (x ∘ Nat.succ) (List.range (k + 1)) = List.map (y ∘ Nat.succ) (List.range (k + 1)) := by
        apply List.map_congr_left
        intro j hj
        rw [List.mem_range] at hj
        exact hxy (j + 1) (by omega) (by omega)
      rw [e]
      ring
  rw [hl, ha, div_add' _ _ _ hK.ne']


-- created on 2026-10-07
