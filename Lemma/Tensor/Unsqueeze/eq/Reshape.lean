import Def.Data.Tensor.Unsqueeze
open List


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.Unsqueeze.eq.Reshape |
| comm | Tensor.Reshape.eq.Unsqueeze |
-/
@[path, comm]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  X.unsqueeze d = X.reshape (s.insertIdx d 1) (by simp [ProdInsertIdx.eq.Prod s d]) := by
-- proof
  rfl


-- created on 2026-07-12
-- updated on 2026-11-20
