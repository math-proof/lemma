import sympy.concrete.continued_fraction

/-!
The continued fraction `alpha` when only the tail `x 1, …, x (n-1)` is positive
(`Lemma/Finset/Eq/Alpha/HK/of/All_Gt_0.py`, where `x 0` is an arbitrary integer).
-/

namespace Continuant

theorem K_congr_H_shift (x y : ℕ → ℝ) (n : ℕ) (hxy : ∀ j, 1 ≤ j → j < n → x j = y j) :
    ∀ m, m + 1 ≤ n → (K x m = K y m ∧ H x m = H y m + (x 0 - y 0) * K y m) ∧
      (K x (m + 1) = K y (m + 1) ∧ H x (m + 1) = H y (m + 1) + (x 0 - y 0) * K y (m + 1)) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨⟨rfl, by simp [H, K]⟩, rfl, by simp [H, K]⟩
  | succ m ih =>
    intro hm
    obtain ⟨h0, h1⟩ := ih (by omega)
    refine ⟨h1, ?_⟩
    have e := hxy (m + 1) (by omega) (by omega)
    show K x (m + 1) * x (m + 1) + K x m = K y (m + 1) * y (m + 1) + K y m ∧
      H x (m + 1) * x (m + 1) + H x m = H y (m + 1) * y (m + 1) + H y m + (x 0 - y 0) * (K y (m + 1) * y (m + 1) + K y m)
    rw [h0.1, h1.1, h0.2, h1.2, e]
    constructor
    · rfl
    · ring

theorem alpha_eq_of_tail_pos (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (h : ∀ j, 1 ≤ j → j < n → 0 < x j) :
    alpha ((List.range n).map x) = H x n / K x n := by
  let y : ℕ → ℝ := fun j => if 1 ≤ j ∧ j < n then x j else 1
  have hy : ∀ j, 0 < y j := by
    intro j
    by_cases hj : 1 ≤ j ∧ j < n
    · simp only [y, if_pos hj]
      exact h j hj.1 hj.2
    · simp only [y, if_neg hj]
      exact one_pos
  have hxy : ∀ j, 1 ≤ j → j < n → x j = y j := by
    intro j h1 h2
    simp only [y, if_pos (And.intro h1 h2)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have key := (K_congr_H_shift x y (m + 1) hxy m le_rfl).2
  have hK := (K_nonneg_pos y hy m).2
  have ha := alpha_eq y hy m
  rw [key.1, key.2]
  have hl : alpha ((List.range (m + 1)).map x) = alpha ((List.range (m + 1)).map y) + (x 0 - y 0) := by
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
    cases m with
    | zero =>
      simp [alpha]
    | succ k =>
      rw [alpha_cons _ (by simp), alpha_cons _ (by simp)]
      have e : List.map (x ∘ Nat.succ) (List.range (k + 1)) = List.map (y ∘ Nat.succ) (List.range (k + 1)) := by
        apply List.map_congr_left
        intro j hj
        rw [List.mem_range] at hj
        exact hxy (j + 1) (by omega) (by omega)
      rw [e]
      ring
  rw [hl, ha, div_add' _ _ _ hK.ne']

end Continuant
