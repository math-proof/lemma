import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.GetAppend.eq.Get.of.GtLength
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.Nat.EqMax
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.SEqFromVectorS.of.SEq
import Lemma.Tensor.SEqToVectorS.of.Eq
import Lemma.Tensor.SEqToVectorS.of.SEq
import Lemma.Vector.SEqMap₂S.of.All_Eq.SEq.SEq
import sympy.tensor.tensor
open Bool List Nat Tensor Vector


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s s' : List ℕ}
-- given
  (h : s.length > 0)
  (h : s.length = s'.length)
  (h_0 : s[0] = s'[0])
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α (s' ++ [n, k])) :
-- imply
  let Xs : List.Vector (Tensor α (s.tail ++ [m, n])) s[0] := cast
    (by
      congr
      rw [TailAppend.eq.AppendTail.of.GtLength_0 (by grind)]
      rw [HeadD.eq.Get_0.of.GtLength_0 (by grind)]
      rw [GetAppend.eq.Get.of.GtLength (by grind)]
    )
    X.toVector
  let Ys : List.Vector (Tensor α (s'.tail ++ [n, k])) s[0] := cast
    (by
      congr
      rw [TailAppend.eq.AppendTail.of.GtLength_0 (by grind)]
      rw [HeadD.eq.Get_0.of.GtLength_0 (by grind)]
      rw [GetAppend.eq.Get.of.GtLength (by grind)]
      rw [← h_0]
    )
    Y.toVector
  X.broadcast_matmul_rec Y (by grind) ≃ Tensor.fromVector (List.Vector.map₂ (fun X Y => X.broadcast_matmul_rec Y (by grind)) Xs Ys) := by
-- proof
  simp
  match s, s' with
  | [], [] =>
    contradiction
  | s₀ :: s, s'₀ :: s' =>
    conv_lhs => unfold Tensor.broadcast_matmul_rec
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
        have h_s : (s₀ :: s ++ [m, n]) = (s₀ ⊔ s₀ :: s ++ [m, n]) := by simp
        have := GetToVector.eq.Get.fin (cast (congrArg (Tensor α) h_s) X) ⟨t, by grind⟩
        simp at this
        rw [this]
        have h_s' : (s₀ :: s' ++ [n, k]) = (s₀ ⊔ s₀ :: s' ++ [n, k]) := by simp
        have := GetToVector.eq.Get.fin (cast (congrArg (Tensor α) h_s') Y) ⟨t, by grind⟩
        simp at this
        rw [this]
        have := GetToVector.eq.Get.fin X ⟨t, by grind⟩
        simp at this
        rw [this]
        have := GetToVector.eq.Get.fin Y ⟨t, by grind⟩
        simp at this
        rw [this]
        have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by grind) h_s X ⟨t, by grind⟩
        simp at this
        rw [this]
        have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by grind) h_s' Y ⟨t, by grind⟩
        simp at this
        rw [this]
      repeat apply SEqToVectorS.of.Eq (by simp)


-- created on 2026-01-11
