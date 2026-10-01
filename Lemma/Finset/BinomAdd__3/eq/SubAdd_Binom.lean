import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y z : ℕ} :
-- imply
  (((x + y + z).choose 3 : ℕ) : ℤ) = (x.choose 3 : ℤ) + y.choose 3 + z.choose 3 + (x + y).choose 2 * z +
    (y + z).choose 2 * x + (x + z).choose 2 * y - 2 * x * y * z := by
-- proof
  have c2 : ∀ m : ℕ, 2 * (m.choose 2 : ℤ) = m * (m - 1) := by
    intro m
    induction m with
    | zero =>
      simp
    | succ m ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast
      linear_combination ih
  have c3 : ∀ m : ℕ, 6 * (m.choose 3 : ℤ) = m * (m - 1) * (m - 2) := by
    intro m
    induction m with
    | zero =>
      simp
    | succ m ih =>
      rw [Nat.choose_succ_succ]
      push_cast
      linear_combination ih + 3 * c2 m
  have e1 := c3 (x + y + z)
  have e2 := c2 (x + y)
  have e3 := c2 (y + z)
  have e4 := c2 (x + z)
  push_cast at e1 e2 e3 e4
  have key : (6 : ℤ) * ((((x + y + z).choose 3 : ℕ) : ℤ) - ((x.choose 3 : ℤ) + y.choose 3 + z.choose 3 +
      (x + y).choose 2 * z + (y + z).choose 2 * x + (x + z).choose 2 * y - 2 * x * y * z)) = 0 := by
    linear_combination e1 - c3 x - c3 y - c3 z - 3 * (z : ℤ) * e2 - 3 * (x : ℤ) * e3 - 3 * (y : ℤ) * e4
  have := (mul_eq_zero.mp key).resolve_left (by norm_num)
  linarith


-- created on 2022-07-11
