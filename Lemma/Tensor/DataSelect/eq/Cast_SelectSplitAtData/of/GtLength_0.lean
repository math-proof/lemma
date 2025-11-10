import Lemma.Bool.EqCast.of.SEq
import Lemma.List.EqLengthSlice_CoeMul.of.Lt
import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.List.ProdTake.eq.MulProdTake.of.Lt_Length
import Lemma.List.ProdTakeMapCast.eq.CastProdTake
import Lemma.Tensor.DataSelect.as.SelectSplitAtData.of.GtLength
import sympy.tensor.tensor
open Bool List Tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_d : s.length > d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.select ⟨d, h_d⟩ i).data = cast
    (by
      simp
      repeat rw [ProdTakeMapCast.eq.CastProdTake]
      rw [ProdTake.eq.MulProdTake.of.Lt_Length (by omega)]
      rw [EqLengthSlice_CoeMul.of.Lt (by omega)]
      rw [MulProdS.eq.ProdEraseIdx]
    )
    (X.data.splitAt (d + 1))[i :: s[d]].flatten := by
-- proof
  apply Eq_Cast.of.SEq
  apply DataSelect.as.SelectSplitAtData.of.GtLength h_d


-- created on 2025-11-07
-- updated on 2025-11-10
