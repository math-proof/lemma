import Lemma.Int.LeMulS.of.Le.Ge_0
import Lemma.Int.GeNeg_0.of.Le_0
import Lemma.Int.Mul_Neg.eq.NegMul
import Lemma.Int.Le.of.GeNegS
import sympy.Basic'
open Int

/--
using comm 2 instead of comm 1 since conditions of the lemma is arranged according to the constructor of multiplication
| attributes | lemma |
| :---: | :---: |
| main | Int.LeMulS.of.Ge.Le_0 |
| comm 2 | Int.GeMulS.of.Le.Le_0 |
-/
@[main, comm 2]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a b : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : x ≤ 0) :
-- imply
  a * x ≤ b * x := by
-- proof
  have := GeNeg_0.of.Le_0 h₁
  have := GeMulS.of.Ge.Ge_0 h₀ this
  repeat rw [Mul_Neg.eq.NegMul] at this
  apply Le.of.GeNegS this


-- created on 2025-03-23
-- updated on 2025-03-30
