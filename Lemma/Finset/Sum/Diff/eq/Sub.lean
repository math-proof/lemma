import Mathlib.Algebra.Group.ForwardDiff
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma telescope
  {i n : ℤ}
  {x : ℤ → ℝ}
-- given
  (h : i ≤ n + 1) :
-- imply
  ∑ k ∈ Finset.Ico i (n + 1), fwdDiff 1 x k = x (n + 1) - x i := by
-- proof
  obtain ⟨d, hd⟩ : ∃ d : ℕ, n + 1 = i + d := ⟨(n + 1 - i).toNat, by omega⟩
  rw [hd]
  clear hd h
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.cast_succ, ← add_assoc, ← Finset.insert_Ico_right_eq_Ico_add_one (by omega),
      Finset.sum_insert Finset.right_notMem_Ico, ih]
    simp only [fwdDiff]
    ring


-- created on 2023-10-22
