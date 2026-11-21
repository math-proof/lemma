import Theorem.Int.Sub.eq.Add_Neg
import Lemma.Int.EqNegNeg
open Int


/--
| attributes | lemma |
| :---: | :---: |
| path | Int.Add.eq.Sub_Neg |
| comm | Int.Sub_Neg.eq.Add |
-/
@[path, comm]
private lemma main
  [AddGroup α]
-- given
  (a b : α) :
-- imply
  a + b = a - -b := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [EqNegNeg]


-- created on 2025-03-16
-- updated on 2026-11-21
