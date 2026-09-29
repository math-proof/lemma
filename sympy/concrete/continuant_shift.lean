import sympy.concrete.continuant

/-!
Continuant identities used by `Finset.Mul.eq.Add.HK.KH`, `Finset.K.gt.Zero.of.All_Gt_0`:
shifting the argument by one, and positivity from bounded positivity hypotheses.
-/

namespace Continuant

theorem shift_aux (x : ℕ → ℝ) : ∀ m, (K x (m + 1) = H (fun i => x (i + 1)) m ∧
      H x (m + 1) = x 0 * K x (m + 1) + K (fun i => x (i + 1)) m) ∧
    (K x (m + 2) = H (fun i => x (i + 1)) (m + 1) ∧
      H x (m + 2) = x 0 * K x (m + 2) + K (fun i => x (i + 1)) (m + 1)) := by
  intro m
  induction m with
  | zero =>
    refine ⟨⟨rfl, ?_⟩, ?_, ?_⟩
    · show x 0 = x 0 * 1 + 0
      ring
    · show 1 * x 1 + 0 = x (0 + 1)
      ring
    · show x 0 * x 1 + 1 = x 0 * (1 * x 1 + 0) + 1
      ring
  | succ m ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_, ?_⟩
    · show K x (m + 2) * x (m + 2) + K x (m + 1) =
        H (fun i => x (i + 1)) (m + 1) * x (m + 1 + 1) + H (fun i => x (i + 1)) m
      rw [h0.1, h1.1]
    · show H x (m + 2) * x (m + 2) + H x (m + 1) =
        x 0 * (K x (m + 2) * x (m + 2) + K x (m + 1)) +
          (K (fun i => x (i + 1)) (m + 1) * x (m + 1 + 1) + K (fun i => x (i + 1)) m)
      rw [h0.2, h1.2]
      ring

theorem K_succ_eq_H_shift (x : ℕ → ℝ) (m : ℕ) : K x (m + 1) = H (fun i => x (i + 1)) m :=
  (shift_aux x m).1.1

theorem H_succ_eq (x : ℕ → ℝ) (m : ℕ) : H x (m + 1) = x 0 * K x (m + 1) + K (fun i => x (i + 1)) m :=
  (shift_aux x m).1.2

theorem H_pos_aux (x : ℕ → ℝ) : ∀ m, (∀ i < m + 1, 0 < x i) → 0 < H x m ∧ 0 < H x (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro h
    exact ⟨by simp [H], by simpa [H] using h 0 (by omega)⟩
  | succ m ih =>
    intro h
    obtain ⟨h0, h1⟩ := ih (fun i hi => h i (by omega))
    refine ⟨h1, ?_⟩
    show 0 < H x (m + 1) * x (m + 1) + H x m
    exact add_pos (mul_pos h1 (h (m + 1) (by omega))) h0

theorem H_pos_of_lt (x : ℕ → ℝ) (m : ℕ) (h : ∀ i < m, 0 < x i) : 0 < H x m := by
  cases m with
  | zero => simp [H]
  | succ m => exact (H_pos_aux x m h).2

theorem K_pos_aux (x : ℕ → ℝ) : ∀ m, (∀ i, 1 ≤ i → i < m + 1 → 0 < x i) → 0 ≤ K x m ∧ 0 < K x (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨by simp [K], by simp [K]⟩
  | succ m ih =>
    intro h
    obtain ⟨h0, h1⟩ := ih (fun i h1 h2 => h i h1 (by omega))
    refine ⟨h1.le, ?_⟩
    show 0 < K x (m + 1) * x (m + 1) + K x m
    exact add_pos_of_pos_of_nonneg (mul_pos h1 (h (m + 1) (by omega) (by omega))) h0

theorem K_pos_of (x : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (h : ∀ i, 1 ≤ i → i < m → 0 < x i) : 0 < K x m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact (K_pos_aux x k h).2

end Continuant
