import sympy.Basic
open Set Nat


class ClosedUnderAdd (A : Set ℕ) : Prop where
  closed_under_add : ∀ ⦃a b⦄, a ∈ A → b ∈ A → a + b ∈ A


@[main]
private lemma main
  {A : Set ℕ}
  [ClosedUnderAdd A]
  {x n : ℕ}
-- given
  (hn : 0 < n)
  (hx : x ∈ A) :
-- imply
  n * x ∈ A := by
-- proof
  have hA := (inferInstance : ClosedUnderAdd A).closed_under_add
  induction' n using Nat.strongRec with n ih
  cases n with
  | zero => cases hn
  | succ n =>
      have : n = 0 ∨ 0 < n := Nat.eq_zero_or_pos n
      have hstep : (n + 1) * x = n * x + x := by ring
      cases this with
      | inl h0 => rw [h0]; simp [hx]
      | inr hnpos =>
          have hx' : n * x ∈ A := ih n (Nat.lt_succ_self n) hnpos
          simp [hstep, hA hx' hx]


-- created on 2026-09-18
