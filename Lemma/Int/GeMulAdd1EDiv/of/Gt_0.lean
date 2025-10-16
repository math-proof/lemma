import sympy.core.relational
import Lemma.Nat.Eq_AddMulDiv___Mod
import Lemma.Algebra.EqSub.is.Eq_Add
import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Nat.AddAdd
import Lemma.Algebra.LeAddS.is.Le
import Lemma.Nat.LeAdd_1.of.Lt
import Lemma.Nat.LtMod.of.Gt_0
open Algebra Nat


@[main]
private lemma main
-- given
  (h : d > 0)
  (n : ℤ) :
-- imply
  (1 + (n - 1) / d) * d ≥ n := by
-- proof
  -- notice that n / d means the Euclidian division, not rational division
  -- Use the Euclidean division theorem to express n - 1 as d * q + r
  have h₀ := Eq_AddMulDiv___Mod (n := n - 1) (d := d)
  denote h_q : q = (n - 1) / d
  denote h_r : r = (n - 1) % d
  rw [← h_q]
  rw [← h_q, ← h_r] at h₀
  rw [Eq_Add.of.EqSub h₀]
  rw [MulAdd.eq.AddMulS]
  norm_num
  rw [AddAdd.permute]
  apply LeAddS.of.Le (a := q * d)
  apply LeAdd_1.of.Lt
  have := LtMod.of.Gt_0 h (n - 1)
  rwa [← h_r] at this


-- created on 2025-03-29
