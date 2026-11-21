import Def.Data.Tensor.Defs.Part4
import Def.Data.Tensor.Prod
import Theorem.Tensor.GtLength_0.of.GtLength_0
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Theorem.Tensor.Length.eq.Get_0.of.GtLength_0
open Tensor List


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.ProdTake_1.eq.Length.of.GtLength_0 |
| comm | Tensor.Length.eq.ProdTake_1.of.GtLength_0 |
-/
@[path, comm]
private lemma main
  {X : Tensor α s}
-- given
  (h : X.length > 0) :
-- imply
  (s.take 1).prod = X.length := by
-- proof
  have h_s := GtLength_0.of.GtLength_0 h
  rw [ProdTake_1.eq.Get_0.of.GtLength_0 h_s]
  rw [Length.eq.Get_0.of.GtLength_0]


-- created on 2025-10-08
-- updated on 2026-11-20
