import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
import Lemma.Tensor.GetResize_0.as.Get.of.GtLength_0
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.GetAppend.eq.Get.of.GtLength
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.Nat.EqMax
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.SEqFromVectorS.of.SEq
import Lemma.Tensor.SEqToVectorS.of.Eq
import Lemma.Tensor.SEqToVectorS.of.SEq
import Lemma.Vector.SEqMap₂S.of.All_Eq.SEq.SEq
open Bool List Nat Tensor Vector


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h : s.length > 0)
  (h_length : s.length = s'.length)
  (h_0 : s[0] = s'[0])
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α (s' ++ [n, k])) :
-- imply
  let Xs : List.Vector (Tensor α (s ++ [m, n]).tail) s[0] := cast
    (by
      rw [TailAppend.eq.AppendTail.of.GtLength_0 (by grind)]
      rw [HeadD.eq.Get_0.of.GtLength_0 (by grind)]
      rw [GetAppend.eq.Get.of.GtLength (by grind)]
    )
    X.toVector
  let Ys : List.Vector (Tensor α (s' ++ [n, k]).tail) s[0] := cast
    (by
      rw [TailAppend.eq.AppendTail.of.GtLength_0 (by grind)]
      rw [HeadD.eq.Get_0.of.GtLength_0 (by grind)]
      rw [GetAppend.eq.Get.of.GtLength (by grind)]
      rw [← h_0]
    )
    Y.toVector
  X.matmul Y (by grind) ≃ Tensor.fromVector (List.Vector.map₂ (fun X Y => Tensor.matmul (cast (congrArg (Tensor α) (show (s ++ [m, n]).tail = s.tail ++ [m, n] by grind)) X) (cast (congrArg (Tensor α) (show (s' ++ [n, k]).tail = (s'.tail ++ [n, k]) by grind)) Y) (by grind)) Xs Ys) := by
-- proof
  simp
  match s, s' with
  | [], [] =>
    contradiction
  | s₀ :: s, s'₀ :: s' =>
    conv_lhs => unfold Tensor.matmul
    simp
    apply SEqCast.of.SEq.Eq
    ·
      simp [Tensor.broadcast_shape]
      split_ifs with h1 h2
      ·
        simp
        grind
      ·
        simp
        grind
      ·
        simp
    ·
      simp at h_0
      subst h_0
      simp
      apply SEqFromVectorS.of.SEq
      apply SEqMap₂S.of.All_Eq.SEq.SEq
      ·
        intro t
        have h_t := t.isLt
        simp only [EqMax] at h_t
        have := GetToVector.eq.Get.fin (X.resize ⟨0, by grind⟩ (s₀ ⊔ s₀)) ⟨t, by grind⟩
        simp at this
        rw [this]
        have := GetToVector.eq.Get.fin (Y.resize ⟨0, by grind⟩ (s₀ ⊔ s₀)) ⟨t, by grind⟩
        simp at this
        rw [this]
        have := GetToVector.eq.Get.fin X ⟨t, by grind⟩
        simp at this
        rw [this]
        have := GetToVector.eq.Get.fin Y ⟨t, by grind⟩
        simp at this
        rw [this]
        have := GetResize_0.eq.Cast_Get.of.GtLength_0.fin (by grind) X ⟨t, by grind⟩ s₀
        simp at this
        rw [this]
        have := GetResize_0.eq.Cast_Get.of.GtLength_0.fin (by grind) Y ⟨t, by grind⟩ s₀
        simp at this
        rw [this]
      .
        rw [EqMax]
        have := Resize_0.eq.Cast.of.GtLength_0 (by grind) X
        simp at this
        rw [this]
      .
        rw [EqMax]
        have := Resize_0.eq.Cast.of.GtLength_0 (by grind) Y
        simp at this
        rw [this]


-- created on 2026-01-11
