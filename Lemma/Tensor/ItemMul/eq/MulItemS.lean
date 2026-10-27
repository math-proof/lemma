import Def.Data.Holor.Defs.Part4
import Def.Data.Holor.Item
open Vector


@[path]
private lemma main
  [Mul α]
-- given
  (a b : Tensor α []) :
-- imply
  (Mul.mul a b).item = a.item * b.item := by
-- proof
  unfold Tensor.item
  exact GetMul.eq.MulGetS.fin a.data b.data ⟨0, Nat.zero_lt_one⟩


-- created on 2026-09-07
