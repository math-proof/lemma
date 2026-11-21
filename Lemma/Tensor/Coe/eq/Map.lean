import Instance.Data.Tensor.Defs.Part3


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.Coe.eq.Map |
| comm | Tensor.Map.eq.Coe |
-/
@[path, comm]
private lemma main
  [Coe α β]
-- given
  (X : Tensor α s) :
-- imply
  (X : Tensor β s) = X.map Coe.coe := by
-- proof
  cases X
  simp [Tensor.map]


-- created on 2026-07-28
-- updated on 2026-11-20
