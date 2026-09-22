import Lemma.Nat.Le.of.Lt
import Lemma.Int.Ge0Sub.is.Le
import Lemma.Int.Le0Mul.of.Le_0.Le_0
import Lemma.Int.MulSub.eq.SubMulS
import Lemma.Int.Le0Sub.is.Ge
open Nat Int

/--
| attributes | lemma |
| :---: | :---: |
| main | Int.GeMulS.of.Le.Lt_0 |
| comm 2 | Int.LeMulS.of.Ge.Lt_0 |
-/
@[main, comm 2]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a b : α}
-- given
  (h₁ : a ≤ b)
  (h₀ : x < 0) :
-- imply
  a * x ≥ b * x := by
-- proof
  have h₂ := Le.of.Lt h₀
  have h₃ := Ge0Sub.of.Le h₁
  have h₄ := Le0Mul.of.Le_0.Le_0 h₃ h₂
  rw [MulSub.eq.SubMulS] at h₄
  apply Ge.of.Le0Sub h₄


-- created on 2019-05-21
-- updated on 2026-09-21
