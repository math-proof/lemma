import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Int.EqToNat
open Nat Int


@[main]
private lemma main
-- given
  (i d : ℕ) :
-- imply
  (i + (d : ℤ)).toNat = i + d := by
-- proof
  have := AddCoeS.eq.CoeAdd (α := ℤ) i d
  rw [this]
  rw [EqToNat]


-- created on 2025-10-20
