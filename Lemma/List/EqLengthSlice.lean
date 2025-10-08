import stdlib.Slice
import Lemma.Algebra.EqAdd_Mul_DivSub1Sign_2
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Int.EqToNat
open Algebra Int Nat


@[main]
private lemma main
-- given
  (n i : Nat) :
-- imply
  (⟨i, n + i, 1⟩ : Slice).length (n + i) = n := by
-- proof
  unfold Slice.length
  simp [EqAdd_Mul_DivSub1Sign_2]
  rw [AddCoeS.eq.CoeAdd]
  rw [EqAdd_Mul_DivSub1Sign_2]
  simp only [EqToNat]
  simp
  rw [AddCoeS.eq.CoeAdd]
  simp only [EqToNat]
  simp


@[main]
private lemma coe
-- given
  (n i : Nat) :
-- imply
  (⟨i, (n + i:ℕ), 1⟩ : Slice).length (n + i) = n := by
-- proof
  rw [CoeAdd.eq.AddCoeS]
  apply main


-- created on 2025-05-23
