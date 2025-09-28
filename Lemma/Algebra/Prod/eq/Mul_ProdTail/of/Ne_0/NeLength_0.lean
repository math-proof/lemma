import Lemma.Algebra.Eq_Cons_Tail.of.NeLength_0
import Lemma.Algebra.ProdCons.eq.Mul_Prod
open Algebra


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h₀: s.length ≠ 0)
  (h₁: s[0] ≠ 0) :
-- imply
  s.prod = s[0] * s.tail.prod := by
-- proof
  have h_prod : (s[0]::s.tail).prod = s[0] * s.tail.prod := by
    simp
  rw [← Eq_Cons_Tail.of.NeLength_0 h₀] at h_prod
  exact h_prod


-- created on 2024-07-01
