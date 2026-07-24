import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength
import sympy.tensor.tensor
open Bool List


@[main]
private lemma simp
  {s : List ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.select ⟨d, h⟩ i).data ≃ (X.data.splitAt (d + 1))[i : (s.take (d + 1)).prod : s[d]].flatten := by
-- proof
  unfold Tensor.select
  simp
  apply SEqCast.of.SEq.Eq (List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp h i.isLt)
  rfl


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.select ⟨d, h⟩ i).data ≃ (X.data.splitAt (d + 1))[i :: s[d]].flatten := by
-- proof
  apply simp


-- created on 2025-11-10
-- updated on 2026-07-23
