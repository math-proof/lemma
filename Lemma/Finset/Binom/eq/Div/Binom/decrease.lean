import sympy.functions.combinatorial.factorials
import sympy.Basic


@[path]
private lemma main
  {n k : ℕ}
-- given
  (h : k < n) :
-- imply
  Nat.choose n k = Nat.choose (n - 1) k * n / (n - k) := by
-- proof
  have hnk : n - k ≠ 0 := by omega
  have hid := Nat.choose_mul_succ_eq (n - 1) k
  rw [show n - 1 + 1 = n from by omega] at hid
  exact (Nat.div_eq_of_eq_mul_left (by omega) hid).symm


-- created on 2020-10-07
-- updated on 2023-06-03
