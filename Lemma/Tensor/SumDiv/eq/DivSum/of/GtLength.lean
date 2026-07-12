import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataDiv.eq.DivData
import Lemma.Vector.CastSum.eq.DivCastSumSplitAt_1
import Lemma.Tensor.ToVectorDiv.eq.DivToVector_Reshape
import Lemma.Vector.MapMap.eq.Map_Comp
import Lemma.Nat.Div.eq.HDiv
import Lemma.Tensor.Div.eq.Div_Broadcast
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Nat.Any_Eq_AddMul
open Tensor Vector Nat


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
    unfold Tensor.sum
    simp [h]
    apply Eq.of.EqDataS
    let ⟨data⟩ := X
    repeat rw [DataDiv.eq.DivData]
    rw [CastSum.eq.DivCastSumSplitAt_1]
  | succ dim ih =>
    unfold Tensor.sum
    simp [h]
    match s with
    | .nil =>
      contradiction
    | s₀ :: s =>
      rw [ToVectorDiv.eq.DivToVector_Reshape]
      simp [HDiv.hDiv]
      apply Eq.of.EqDataS
      simp [Div.eq.HDiv]
      simp at h
      have h_sum : ∀ x : Tensor α s, (x / n.reshape s (by simp)).sum dim = x.sum dim / n := fun x => by
        simpa [Div_Broadcast.eq.Div] using ih h x
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
      ext k
      rw [GetMap.eq.UFnGet]
      let ⟨i, j, h_k⟩ := Any_Eq_AddMul k
      repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_k]
      simp
      rw [DataDiv.eq.DivData]
      rw [GetDiv.eq.DivGet.fin (a := n.data[0])]
      rfl


-- created on 2025-09-25
