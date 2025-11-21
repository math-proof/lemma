import Lemma.Nat.Add
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Ne_0
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.Mod_Mul.eq.Add_Mul_ModDiv
open Nat


/--
similar with Ordinal.mul\_add\_mod\_mul
-/
@[main]
private lemma ord
-- given
  (h : r < d)
  (q n : ℕ) :
-- imply
  (d * q + r) % (d * n) = d * (q % n) + r := by
-- proof
  rw [Mod_Mul.eq.Add_Mul_ModDiv]
  simp [Add.comm, EqMod.of.Lt h]
  left
  rw [Add.comm]
  rw [DivAddMul.eq.Add_Div.of.Ne_0.left (by omega)]
  simp [Div.eq.Zero.of.Lt h]


@[main]
private lemma main
-- given
  (h : r < d)
  (q n : ℕ) :
-- imply
  (q * d + r) % (n * d) = q % n * d + r := by
-- proof
  have := ord h q n
  rw [Mul.comm] at this
  rw [Mul.comm (a := n)]
  rw [this]
  rw [Mul.comm]


-- created on 2025-11-21
