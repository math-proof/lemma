import sympy.tensor.tensor
import Lemma.Vector.EqFlattenUnflatten
import Lemma.Bool.EqUFnS.of.Eq
import Lemma.Algebra.Ge.of.NotLt
import Lemma.Vector.EqGetRange
import Lemma.Algebra.EqDivMul.of.Ne_0
import Lemma.Algebra.Ne.of.Gt
import Lemma.Algebra.NotGt.is.Le
import Lemma.Algebra.Eq_0.of.Le_0
import Lemma.Logic.EqCast.of.Eq
import Lemma.Vector.ArraySlice.as.GetSplitAt_1.of.Lt_Get_0.GtLength_0.Eq_ProdTail
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.Bool.EqCast.of.SEq
open Algebra Logic Vector Bool


@[main]
private lemma main
-- given
  (t : Tensor α (s₀ :: s)) :
-- imply
  t.data = ((List.Vector.range s₀).map fun i => t[i].data).flatten := by
-- proof
  let data : List.Vector α (s₀ * s.prod) := t.data
  have h_data : t.data = data := rfl
  rw [h_data, Eq_FlattenUnflatten data]
  apply EqUFnS.of.Eq _ List.Vector.flatten
  rw [List.Vector.unflatten]
  congr
  funext i
  simp [GetElem.getElem, Tensor.get, Tensor.toVector]
  rw [h_data]
  apply EqCast.of.SEq
  have := ArraySlice.as.GetSplitAt_1.of.Lt_Get_0.GtLength_0.Eq_ProdTail (s := s₀ :: s) (n := s.prod) (i := i) (by simp_all) (by simp_all) (by simp_all) data
  apply SEq.of.SEq.SEq this
  rw [GetCast_Map.eq.UFnGet.of.Eq.Lt.fin _ (by simp)]
  simp [GetElem.getElem]
  rfl


-- created on 2025-05-06
-- updated on 2025-05-18
