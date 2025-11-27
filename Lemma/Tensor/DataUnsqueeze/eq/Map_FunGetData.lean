import Lemma.List.ProdInsertIdx.eq.Prod
import sympy.tensor.tensor
open List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.unsqueeze d).data = (List.Vector.range (s.insertIdx d 1).prod).map fun i => X.data[cast (congrArg Fin (ProdInsertIdx.eq.Prod s d)) i] := by
-- proof
  simp [Tensor.unsqueeze]


@[main]
private lemma fin
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.unsqueeze d).data = (List.Vector.range (s.insertIdx d 1).prod).map fun i => X.data.get (cast (congrArg Fin (ProdInsertIdx.eq.Prod s d)) i) := by
-- proof
  apply main


-- created on 2025-11-27
