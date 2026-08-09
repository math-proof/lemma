import stdlib.Slice
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Nat.CoeMin.eq.MinCoeS
import Lemma.Int.EqToNat
import Lemma.Nat.EqCeilCoe
open Int Nat


@[main]
private lemma main
-- given
  (n m j : ℕ) :
-- imply
  (⟨j, n, 1⟩ : Slice).length m = n ⊓ m - j := by
-- proof
  unfold Slice.length
  simp [EqAdd_Mul_DivSub1Sign_2]
  rw [MinCoeS.eq.CoeMin]
  simp only [EqToNat, EqCeilCoe]


-- created on 2026-08-09
