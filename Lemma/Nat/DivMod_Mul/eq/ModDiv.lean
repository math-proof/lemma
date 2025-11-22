import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.LtDiv.of.Lt_Mul
import Lemma.Nat.LtMod.of.Ne_0
import Lemma.Nat.ModDivMod_Mul.eq.ModDiv
import Lemma.Nat.Mul.eq.Zero.is.OrEqS_0
import Lemma.Nat.Mul
open Nat


@[main]
private lemma main
-- given
  (m n d : ℕ) :
-- imply
  m % (n * d) / n = m / n % d := by
-- proof
  if h : n * d = 0 then
    obtain h_0 | h_0 := OrEqS_0.of.Mul.eq.Zero h <;>
    .
      subst h_0
      simp
  else
    rw [← ModDivMod_Mul.eq.ModDiv]
    rw [Mul.comm (a := d)]
    apply Eq.symm
    apply EqMod.of.Lt
    apply LtDiv.of.Lt_Mul.left
    apply LtMod.of.Ne_0 h


-- created on 2025-11-22
