import sympy.core.relational
import Lemma.Nat.Eq_AddMulDiv___Mod
import Lemma.Int.EqSub.is.Eq_Add
import Lemma.Int.MulSub.eq.SubMulS
import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Algebra.LeAddS.is.Le
import Lemma.Nat.LeAdd_1.of.Lt
import Lemma.Int.Mod.lt.Neg.of.Lt_0
open Algebra Nat Int


@[main]
private lemma main
-- given
  (h : d < 0)
  (n : ℤ) :
-- imply
  ((n - 1) / d - 1) * d ≥ n := by
-- proof
  have h₀ := Eq_AddMulDiv___Mod (n := n - 1) (d := d)
  denote h_q : q = (n - 1) / d
  denote h_r : r = (n - 1) % d
  rw [← h_q]
  rw [← h_q, ← h_r] at h₀
  have := Eq_Add.of.EqSub h₀
  rw [this]
  rw [MulSub.eq.SubMulS]
  norm_num
  rw [Sub.eq.Add_Neg]
  rw [AddAdd.eq.Add_Add]
  apply LeAddS.of.Le.left (a := q * d)
  apply LeAdd_1.of.Lt
  have := Mod.lt.Neg.of.Lt_0 h (n - 1)
  rwa [← h_r] at this


-- created on 2025-03-29
-- updated on 2025-04-30
