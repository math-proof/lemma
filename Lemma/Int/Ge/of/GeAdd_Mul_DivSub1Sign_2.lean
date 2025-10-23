import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
open Nat


@[main]
private lemma main
  {n : ℕ}
  {i : ℤ}
-- given
  (h : Slice.Add_Mul_DivSub1Sign_2 n i ≥ n) :
-- imply
  i ≥ n := by
-- proof
  match i with
  | .ofNat i =>
    simp [EqAdd_Mul_DivSub1Sign_2 n i] at h
    simp
    assumption
  | .negSucc i =>
    unfold Slice.Add_Mul_DivSub1Sign_2 at h
    simp at h


-- created on 2025-05-11
