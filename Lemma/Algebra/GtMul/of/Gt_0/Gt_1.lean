import Lemma.Algebra.GtMulS.of.Gt_0.Gt
import Lemma.Algebra.EqMul_1
open Algebra


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a t : α}
-- given
  
  (h₀ : a > 0) 
  (h₁ : t > 1):
-- imply
  a * t > a := by
-- proof
  have h := GtMulS.of.Gt_0.Gt h₀ h₁
  rw [EqMul_1] at h
  assumption


-- created on 2025-10-01
