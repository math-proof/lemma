import sympy.functions.combinatorial.factorials
import sympy.Basic


@[path]
private lemma main
  {n k : ℕ} :
-- imply
  Nat.choose n k = Nat.choose (n + 1) k * (n + 1 - k) / (n + 1) := by
-- proof
  have hid := Nat.choose_mul_succ_eq n k
  exact (Nat.div_eq_of_eq_mul_left (by omega) hid.symm).symm


-- created on 2023-06-03
