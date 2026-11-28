import Theorem.Tensor.Length.eq.Get_0.of.GtLength_0
import Theorem.Tensor.Length.eq.Get_0.of.Ne_Nil
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.Length.eq.Get_0.of.GtLength_0 |
| comm | Tensor.Get_0.eq.Length.of.GtLength_0 |
-/
@[comm]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.length = s[0] := by
-- proof
  simp [Length.eq.Get_0.of.Ne_Nil (List.length_pos_iff.mp h)]


-- created on 2025-06-14
-- updated on 2026-11-20
