import Mathlib
import sympy.Basic
import Def.NumberTheory.GibonacciNumber
import Lemma.Nat.GibonacciNumber


namespace MetaMathlibExt

/--
[gibonacci_cassini_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GibonacciCassini.lean)
-/
@[path]
lemma gibonacci_cassini_of_pos
  {G₀ G₁ : ℤ}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  gibonacciNumber G₀ G₁ (n + 1) * gibonacciNumber G₀ G₁ (n - 1) -
    (gibonacciNumber G₀ G₁ n) ^ 2 =
    (-1 : ℤ) ^ n * (G₁ ^ 2 - G₀ * G₁ - G₀ ^ 2) := by
-- proof
  have hrec : ∀ m, gibonacciNumber G₀ G₁ (m + 2) =
    gibonacciNumber G₀ G₁ (m + 1) + gibonacciNumber G₀ G₁ m :=
    fun m => rfl
  have g0 : gibonacciNumber G₀ G₁ 0 = G₀ := rfl
  have g1 : gibonacciNumber G₀ G₁ 1 = G₁ := rfl
  have g2 : gibonacciNumber G₀ G₁ 2 =
    gibonacciNumber G₀ G₁ 1 + gibonacciNumber G₀ G₁ 0 := rfl
  have base : gibonacciNumber G₀ G₁ 0 * gibonacciNumber G₀ G₁ 2 -
    gibonacciNumber G₀ G₁ 1 ^ 2 =
    -(-1 : ℤ) ^ 0 * (G₁ ^ 2 - G₀ * G₁ - G₀ ^ 2) := by
    rw [g0, g1, g2, g0, g1]
    ring
  have step : ∀ j, gibonacciNumber G₀ G₁ (j + 1) *
    gibonacciNumber G₀ G₁ (j + 3) -
    gibonacciNumber G₀ G₁ (j + 2) ^ 2 =
    -(gibonacciNumber G₀ G₁ j * gibonacciNumber G₀ G₁ (j + 2) -
      gibonacciNumber G₀ G₁ (j + 1) ^ 2) := by
    intro j
    have r1 := hrec j
    have r2 := hrec (j + 1)
    have e1 : j + 1 + 2 = j + 3 := by omega
    have e2 : j + 1 + 1 = j + 2 := by omega
    rw [e1, e2] at r2
    linear_combination (gibonacciNumber G₀ G₁ (j + 1)) * r2 -
      (gibonacciNumber G₀ G₁ (j + 2)) * r1
  have E : ∀ j, gibonacciNumber G₀ G₁ j *
    gibonacciNumber G₀ G₁ (j + 2) -
    gibonacciNumber G₀ G₁ (j + 1) ^ 2 =
    -(-1 : ℤ) ^ j * (G₁ ^ 2 - G₀ * G₁ - G₀ ^ 2) := by
    intro j
    induction j with
    | zero =>
      have e1 : 0 + 2 = 2 := by omega
      have e2 : 0 + 1 = 1 := by omega
      rwa [e1, e2]
    | succ j ih =>
      have e1 : j + 1 + 2 = j + 3 := by omega
      have e2 : j + 1 + 1 = j + 2 := by omega
      rw [e1, e2]
      have pw : (-1 : ℤ) ^ (j + 1) = -(-1 : ℤ) ^ j := by
        rw [pow_succ]
        ring
      rw [step j, ih, pw]
      ring
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e0 : 1 + m = m + 1 := by omega
  have e1 : 1 + m - 1 = m := by omega
  have e2 : 1 + m + 1 = m + 2 := by omega
  rw [e1, e2, e0]
  have pw : (-1 : ℤ) ^ (m + 1) = -(-1 : ℤ) ^ m := by
    rw [pow_succ]
    ring
  rw [pw]
  have hE := E m
  linear_combination hE

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
