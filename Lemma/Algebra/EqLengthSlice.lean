import stdlib.Slice
import Lemma.Algebra.EqAdd_Mul_DivSub1Sign_2
import Lemma.Algebra.CoeAdd.eq.AddCoeS
import Lemma.Algebra.EqToNat
open Algebra


@[main]
private lemma main
-- given
  (n i : Nat) :
-- imply
  (⟨i, n + i, 1⟩ : Slice).length (n + i) = n := by
-- proof
  unfold Slice.length
  simp [EqAdd_Mul_DivSub1Sign_2]
  rw [AddCoeS.eq.CoeAdd.nat]
  rw [EqAdd_Mul_DivSub1Sign_2]
  simp only [EqToNat]
  simp
  rw [AddCoeS.eq.CoeAdd.nat]
  simp only [EqToNat]
  simp


@[main]
private lemma coe
-- given
  (n i : Nat) :
-- imply
  (⟨i, (n + i:ℕ), 1⟩ : Slice).length (n + i) = n := by
-- proof
  rw [CoeAdd.eq.AddCoeS.nat]
  apply main


-- created on 2025-05-23
