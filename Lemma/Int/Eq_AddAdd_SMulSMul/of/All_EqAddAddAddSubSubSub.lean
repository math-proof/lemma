import Mathlib
import sympy.Basic


/--
[AddCommGroup_apply_zsmul_add_eq_of_forall_cube](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddCommGroup_apply_zsmul_add_eq_of_forall_cube.lean)
-/

private lemma tri_succ
  (n : ℤ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  have h : (n + 1) * (n + 1 - 1) = n * (n - 1) + n * 2 := by ring
  rw [h, Int.add_mul_ediv_right _ _ two_ne_zero]

private lemma tri_zero : (0 : ℤ) * (0 - 1) / 2 = 0 := by norm_num

private lemma eq_of_second_difference
  {M N : Type*}
  [AddCommGroup M]
  [AddCommGroup N]
  (g : ℤ → N) (D : N)
  (h : ∀ n : ℤ, g (n + 2) - 2 • g (n + 1) + g n = D) (n : ℤ) :
  g n = g 0 + n • (g 1 - g 0) + (n * (n - 1) / 2) • D := by

  have h1 : ∀ n : ℤ, g (n + 1) - g n = (g 1 - g 0) + n • D := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
      have hk := h k
      have e : (k : ℤ) + 1 + 1 = k + 2 := by ring
      rw [e]

      have : g (k + 2) - g (k + 1) = (g (k + 1) - g k) + D := by
        rw [← hk]; abel
      rw [this, ih, add_smul, one_smul]
      abel
    | pred k ih =>

      have hk := h (-(k : ℤ) - 1)
      have e1 : (-(k : ℤ) - 1 + 2) = -k + 1 := by ring
      have e2 : (-(k : ℤ) - 1 + 1) = -k := by ring
      rw [e1, e2] at hk
      rw [e2]
      have : g (-(k : ℤ)) - g (-k - 1) = (g (-k + 1) - g (-k)) - D := by
        rw [← hk]; abel
      rw [this, ih, sub_smul, one_smul]
      abel
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have := h1 k
    rw [tri_succ, add_smul, eq_add_of_sub_eq' this |>.trans (by rfl), ih, add_smul, one_smul]
    abel
  | pred k ih =>
    have hk := h1 (-(k : ℤ) - 1)
    have e2 : (-(k : ℤ) - 1 + 1) = -k := by ring
    rw [e2] at hk

    have : g (-(k : ℤ) - 1) = g (-k) - ((g 1 - g 0) + (-(k : ℤ) - 1) • D) := by
      rw [← hk]; abel
    rw [this, ih]
    have ht : (-(k : ℤ)) * (-(k : ℤ) - 1) / 2 = (-(k : ℤ) - 1) * (-(k : ℤ) - 1 - 1) / 2 + (-(k : ℤ) - 1) := by
      have := tri_succ (-(k : ℤ) - 1)
      rwa [e2] at this
    rw [ht, add_smul, sub_smul, sub_smul, one_smul]
    abel

private lemma main_aux
  {M N : Type*}
  [AddCommGroup M]
  [AddCommGroup N]
  (Λ : M → N)
  (hΛ : ∀ x y z : M, Λ (x + y + z) - Λ (x + y) - Λ (x + z) - Λ (y + z) + Λ x + Λ y + Λ z = Λ 0)
  (x y : M) (n : ℤ) :
  Λ (n • x + y) = Λ y + n • (Λ (x + y) - Λ y) + (n * (n - 1) / 2) • (Λ (2 • x) - 2 • Λ x + Λ 0) := by
  set g : ℤ → M := fun n => n • x + y with hg
  have h2 : ∀ n : ℤ, Λ (g (n + 2)) - 2 • Λ (g (n + 1)) + Λ (g n) = Λ (2 • x) - 2 • Λ x + Λ 0 := by
    intro n
    have hc := hΛ (n • x + y) x x
    have e1 : n • x + y + x + x = g (n + 2) := by simp only [hg]; module
    have e2 : n • x + y + x = g (n + 1) := by simp only [hg]; module
    have e3 : x + x = 2 • x := (two_nsmul x).symm
    rw [e1, e2, e3] at hc
    have e4 : Λ (g n) = Λ (n • x + y) := rfl

    rw [two_nsmul (Λ (g (n + 1))), two_nsmul (Λ x)]
    have := hc

    calc _ = (Λ (g (n + 2)) - Λ (g (n + 1)) - Λ (g (n + 1)) - Λ (2 • x) + Λ (n • x + y) + Λ x + Λ x) + (Λ (2 • x) - (Λ x + Λ x)) := by rw [e4]; abel
      _ = Λ 0 + (Λ (2 • x) - (Λ x + Λ x)) := by rw [this]
      _ = Λ (2 • x) - (Λ x + Λ x) + Λ 0 := by abel
  have hmain := @eq_of_second_difference M N _ _ (fun n => Λ (g n)) (Λ (2 • x) - 2 • Λ x + Λ 0) h2 n
  have g0 : g 0 = y := by simp [hg]
  have g1 : g 1 = x + y := by simp [hg]
  simp only [g0, g1] at hmain
  exact hmain

@[path]
private lemma main
  [AddCommGroup M]
  [AddCommGroup N]
  {Λ : M → N}
  {x y : M}
  {n : ℤ}
-- given
  (hΛ : ∀ x y z : M, Λ (x + y + z) - Λ (x + y) - Λ (x + z) - Λ (y + z) + Λ x + Λ y + Λ z = Λ 0) :
-- imply
  Λ (n • x + y) =
      Λ y + n • (Λ (x + y) - Λ y) + (n * (n - 1) / 2) • (Λ (2 • x) - 2 • Λ x + Λ 0) :=
-- proof
  main_aux Λ hΛ x y n


-- created on 2026-10-09
