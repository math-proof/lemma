import Mathlib.Data.Nat.Basic
import sympy.Basic


@[main]
private lemma main
  {α : Type*} [LinearOrder α]
  {f : ℕ → α}
  -- given
  (h : ∀ n : ℕ, f n ≤ f (n + 1))
  -- imply
  : ∀ m n : ℕ, m ≤ n → f m ≤ f n := by
  -- proof
  intro m n hmn
  induction n with
  | zero =>
    have h0 : m = 0 := by omega
    rw [h0]
  | succ n ih =>
    by_cases hmn' : m ≤ n
    · exact le_trans (ih hmn') (h n)
    · have hmeq : m = n + 1 := by omega
      rw [hmeq]

-- created on 2019-05-25
