import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Tensor.DataUnsqueeze.eq.Map_FunGetData
import Lemma.Tensor.Eq.is.EqDataS
open List Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  X.unsqueeze d = ⟨(List.Vector.range (s.insertIdx d 1).prod).map fun i => X.data[cast (congrArg Fin (ProdInsertIdx.eq.Prod s d)) i]⟩ := by
-- proof
  apply Eq.of.EqDataS
  simp
  apply DataUnsqueeze.eq.Map_FunGetData


-- created on 2025-11-30
