import Def.Data.Holor.Defs.Part4
import Def.Data.Holor.Stack.Part2


@[path]
private lemma main
  {x y : Tensor (Fin n) [n]}
  {a : Tensor α [n]}
-- given
  (h : x = y) :
-- imply
  [i < n] a[x[i]] = [i < n] a[y[i]] := by
-- proof
  rw [h]


-- created on 2021-08-26
