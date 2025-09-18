import Lemma.Algebra.EqCoeS.is.Eq
import Lemma.Algebra.EqToNat.of.Ge_0
import Lemma.Algebra.Add.ge.Zero.of.Ge_0.Ge_0
import Lemma.Algebra.CoeAdd.eq.AddCoeS
open Algebra


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n ≥ 0)
  (m : ℕ) :
-- imply
  n.toNat + m = (n + m).toNat := by
-- proof
  apply Eq.of.EqCoeS.nat (R := ℤ)
  rw [EqToNat.of.Ge_0]
  ·
    rw [CoeAdd.eq.AddCoeS.nat]
    rwa [EqToNat.of.Ge_0]
  ·
    apply Add.ge.Zero.of.Ge_0.Ge_0 h
    simp


-- created on 2025-07-14
