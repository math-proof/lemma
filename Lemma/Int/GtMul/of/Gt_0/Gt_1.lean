import Lemma.Nat.GtMulS.of.Gt_0.Gt
import Lemma.Nat.EqMul_1
open Nat


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
  rwa [EqMul_1] at h


-- created on 2025-10-01
