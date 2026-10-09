import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.Min.eq.Zero.of.OrEqS_0 |
| Or.inl | Nat.Min.eq.Zero.of.Eq_0 |
-/
@[path, Or.inl]
private lemma main
  {n m : ℕ}
-- given
  (h : n = 0 ∨ m = 0) :
-- imply
  n ⊓ m = 0 := by
-- proof
  omega


-- created on 2025-08-04
