import Lemma.Bool.EqCast.of.SEq
import Lemma.Nat.Any_Eq_AddMul
import Lemma.Nat.Div.eq.HDiv
import Lemma.Tensor.DataDiv.eq.DivData
import Lemma.Tensor.DataSum_0.as.SumSplitAtData
import Lemma.Tensor.Div.eq.Div_Reshape
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.GetDiv.eq.DivGet
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.Sum.as.FromVectorMapToVector.of.GtLength_0
import Lemma.Tensor.Sum.eq.FromVectorMapToVector
import Lemma.Tensor.ToVectorDiv.eq.DivToVector_Reshape
import Lemma.Vector.CastSum.eq.DivCastSumSplitAt_1
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.MapMap.eq.Map_Comp
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Nat Tensor Vector


@[main]
private lemma main
  [DivisionSemiring α]
-- given
  (h : s.length > dim)
  (X : Tensor α s)
  (n : Tensor α []) :
-- imply
  (X / n).sum dim = X.sum dim / n := by
-- proof
  induction dim generalizing X s with
  | zero =>
    apply Eq.of.EqDataS
    erw [DataSum_0.eq.Cast_SumSplitAtData]
    conv_rhs => erw [DataDiv.eq.DivData]
    conv_rhs => erw [DataSum_0.eq.Cast_SumSplitAtData]
    have := CastSum.eq.DivCastSumSplitAt_1 X.data n.data[0]
    simp at this
    let ⟨data⟩ := X
    simp at this
    simpa
  | succ dim ih =>
    erw [Sum.eq.Cast_FromVectorMapToVector.of.GtLength_0 (by grind)]
    apply EqCast.of.SEq
    match s with
    | .nil =>
      contradiction
    | s₀ :: s =>
      rw [ToVectorDiv.eq.DivToVector_Reshape]
      simp [HDiv.hDiv]
      apply SEq.of.SEqDataS.Eq (by grind)
      simp [Div.eq.HDiv]
      simp at h
      have h_sum : ∀ x : Tensor α s, (x / n.reshape s (by simp)).sum dim = x.sum dim / n := fun x => by
        simpa [Div_Reshape.eq.Div] using ih h x
      erw [funext h_sum]
      have h_fun : (fun x : Tensor α s ↦ x.sum dim / n) = (fun x : Tensor α (s.eraseIdx dim) => x / n) ∘ (fun x : Tensor α s => x.sum dim) := by
        funext x
        simp
      simp [h_fun]
      simp only [Map_Comp.eq.MapMap]
      unfold Tensor.fromVector
      simp
      have h_data : (fun x : Tensor α s => (x.sum dim / n).data) =
          (fun x : Tensor α (s.eraseIdx dim) => (x / n).data) ∘ (fun x : Tensor α s => x.sum dim) := by
        funext x
        simp
      simp only [h_data, Map_Comp.eq.MapMap]
      have h_fun : (fun x : Tensor α (s.eraseIdx dim) ↦ (x / n).data) = (fun x : Tensor α (s.eraseIdx dim) => x.data) ∘ (fun x => x / n) := by
        funext x
        simp
      simp only [h_fun, Map_Comp.eq.MapMap]
      have h_fun : (fun x : Tensor α (s.eraseIdx dim) => x.data) = Tensor.data := by
        simp
      simp only [h_fun]
      apply SEq.of.All_EqGetS.Eq.fin (by rfl)
      intro k
      rw [GetMap.eq.UFnGet]
      let ⟨i, j, h_k⟩ := Any_Eq_AddMul k
      repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_k]
      simp
      rw [DataDiv.eq.DivData]
      rw [GetDiv.eq.DivGet.fin (a := n.data[0])]
      erw [GetToVector.eq.Get.fin]
      congr 1
      rw [Sum.eq.FromVectorMapToVector X dim]
      unfold Tensor.fromVector
      simp
      repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_k]
      simp
      erw [GetToVector.eq.Get.fin]


-- created on 2025-09-25
-- updated on 2026-07-22
