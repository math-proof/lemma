import stdlib.Slice
import Lemma.Algebra.EqAdd_Mul_DivSub1Sign_2
import Lemma.Algebra.CoeMin.eq.MinCoeS
import Lemma.Int.EqToNat
import Lemma.Nat.EqCeilCoe
open Algebra Int Nat


@[main]
private lemma main
-- given
  (n m : ℕ) :
-- imply
  (⟨0, n, 1⟩ : Slice).length m = n ⊓ m := by
-- proof
  unfold Slice.length
  simp [EqAdd_Mul_DivSub1Sign_2]
  rw [MinCoeS.eq.CoeMin.nat]
  simp only [EqCeilCoe]
  simp only [EqToNat]


-- created on 2025-08-04
-- updated on 2025-10-08
