import Lemma.Nat.EqCoeS.is.Eq
import Lemma.Int.EqToNat.of.Ge_0
import Lemma.Nat.Le0Add.of.Ge_0.Ge_0
import Lemma.Nat.CoeAdd.eq.AddCoeS
open Int Nat


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n ≥ 0)
  (m : ℕ) :
-- imply
  n.toNat + m = (n + m).toNat := by
-- proof
  apply Eq.of.EqCoeS (R := ℤ)
  rw [EqToNat.of.Ge_0]
  ·
    rw [CoeAdd.eq.AddCoeS]
    rwa [EqToNat.of.Ge_0]
  ·
    apply Le0Add.of.Ge_0.Ge_0 h
    simp


-- created on 2025-07-14
