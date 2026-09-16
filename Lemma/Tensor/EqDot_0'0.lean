import Lemma.Tensor.EqSum0_0
import Lemma.Nat.EqMul_0'0
import Lemma.Tensor.EqMul_0'0
import Lemma.Tensor.EqBmm_0'0
import Lemma.Tensor.EqMatmul_0'0
import Lemma.Tensor.EqTensordot_0'0
import Lemma.Tensor.Cast_ResizeCast_0.eq.Zero
import Lemma.Tensor.EqEinsum_0'0
import Lemma.Tensor.EqCast_0'0.of.Eq
import Lemma.Tensor.EqTensor0'0
import torch.Tensor.sum
import torch.Tensor.reshape
import torch.Tensor.bmm
import torch.Tensor.repeat
import torch.Tensor.prod
import torch.Tensor.permute
import Lemma.Tensor.EqUnsqueeze0'0
import Lemma.Vector.Flatten0.eq.Zero
import Lemma.Vector.EqCast_0'0.of.Eq
import Lemma.Vector.EqMap0_0.of.EqUFn_0
import Lemma.Vector.Map₂.eq.Zero.of.BFn.eq.Zero
import Lemma.Vector.Repeat0.eq.Zero
import Lemma.Vector.Resize0.eq.Zero
import Lemma.Vector.Transpose0.eq.Zero
import Lemma.Vector.GetSlice0.eq.Zero
import Lemma.Tensor.OfVector0.eq.Zero
import Lemma.Tensor.Resize0.eq.Zero
import Lemma.Tensor.Reshape0.eq.Zero
import Lemma.Tensor.Select0.eq.Zero
import Lemma.Tensor.Repeat0.eq.Zero
import Lemma.Tensor.Rotate0.eq.Zero
import Lemma.Tensor.PermuteHead0.eq.Zero
import Lemma.Tensor.PermuteTail0.eq.Zero
import Lemma.Tensor.Permute0.eq.Zero
import Lemma.Tensor.Transpose0.eq.Zero
import Lemma.Tensor.EqT0'0
import Lemma.Tensor.ToVector0.eq.Zero
import Lemma.Vector.EqAppend0S0
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.List.SetAppend.eq.Append_Set.of.LeLength
import sympy.matrices.expressions.matmul
open Tensor Vector



@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
-- given
  (X : Tensor α s) :
-- imply
  X @ (0 : Tensor α s') = 0 := by
-- proof
  cases s with
  | nil =>
    show Tensor.einsum X (0 : Tensor α s') = _
    unfold Tensor.einsum
    rw [dif_pos (by simp)]
    rw [Tensor.EqMul_0'0.left _]
    exact Tensor.EqCast_0'0.of.Eq (by simp [Tensor.matmul_shape])
  | cons n s₁ =>
    cases s₁ with
    | nil =>
      show Tensor.einsum X (0 : Tensor α s') = _
      unfold Tensor.einsum
      cases s' with
      | nil =>
        rw [dif_neg (by simp), dif_pos (by simp)]
        exact (congrArg (fun t => cast _ t)
          (by
            let i : Fin [].prod := ⟨0, by simp⟩
            change X * (0 : Tensor α []).data[i] = 0
            rw [Tensor.EqData0'0, Vector.EqGet0_0]
            exact Tensor.EqMul_0'0.right X)).trans
          (Tensor.EqCast_0'0.of.Eq (by
            unfold Tensor.matmul_shape
            rw [dif_neg (by simp), dif_pos (by simp)]))
      | cons n' s₂ =>
        cases s₂ with
        | nil =>
          rw [dif_neg (by simp), dif_neg (by simp), dif_pos (by simp)]
          let nn := n ⊔ n'
          let Xr0 : Tensor α [nn] := X.resize ⟨0, by simp⟩ nn
          let Yr0 : Tensor α [nn] := (0 : Tensor α [n']).resize ⟨0, by simp⟩ nn
          have hm : Xr0 * Yr0 = 0 :=
            (congrArg (fun y : Tensor α [nn] => Xr0 * y)
              (Tensor.Resize0.eq.Zero (s := [n']) ⟨0, by simp⟩ nn)).trans
              Nat.EqMul_0'0
          exact (congrArg (fun (p : Tensor α [nn]) => p.sum) hm).trans
            (EqSum0_0 [nn] 0)
        | cons kk0 rest =>
          exact Tensor.EqEinsum_0'0 X n'
    | cons a b =>
      cases s' with
      | nil =>
        have h2 : 2 ≤ (n :: a :: b).length := by simp
        show Tensor.einsum X (0 : Tensor α []) = _
        unfold Tensor.einsum
        rw [dif_neg (by omega), dif_pos (by simp)]
        have hs : (n :: a :: b) = Tensor.matmul_shape (n :: a :: b) [] := by
          unfold Tensor.matmul_shape
          rw [dif_neg (by omega), dif_pos (by simp)]
        exact (congrArg (fun t => cast _ t)
          (by
            let i : Fin [].prod := ⟨0, by simp⟩
            change X * (0 : Tensor α []).data[i] = 0
            rw [Tensor.EqData0'0, Vector.EqGet0_0]
            exact Tensor.EqMul_0'0.right X)).trans
          (Tensor.EqCast_0'0.of.Eq hs)
      | cons n' s₂ =>
        cases s₂ with
        | nil =>
          let s : List ℕ := n :: a :: b
          have h2 : 2 ≤ s.length := by
            change 2 ≤ (n :: a :: b).length
            simp
          show Tensor.einsum X (0 : Tensor α [n']) = _
          unfold Tensor.einsum
          rw [dif_neg (by simp), dif_neg (by simp), dif_neg (by simp),
            dif_pos (by simp)]
          simp (config := { zeta := true }) only []
          let bs := s.take (s.length - 2)
          let k := s[s.length - 2]
          let nn := s[s.length - 1] ⊔ n'
          let X0 : Tensor α (bs ++ [k, s[s.length - 1]]) :=
            cast (by rwa [List.EqAppendTake__ListGet.of.GeLength_2]) X
          let Xr : Tensor α (bs ++ [k, nn]) :=
            cast (congrArg (Tensor α) (by simp))
              (X0.resize ⟨bs.length + 1, by grind⟩ nn)
          let Yt : Tensor α (bs ++ [nn, 1]) :=
            ((0 : Tensor α [n']).resize ⟨0, by grind⟩ nn).reshape
              (bs ++ [nn, 1]) (by simp)
          have hY : Yt = 0 := by
            simp only [Yt]
            rw [Tensor.Resize0.eq.Zero]
            exact Tensor.Reshape0.eq.Zero (by simp)
          have hb : Xr.bmm Yt = 0 :=
            (congrArg (fun Y => Xr.bmm Y) hY).trans (Tensor.EqBmm_0'0 Xr)
          let or : Fin (bs ++ [k, 1]).length :=
            ⟨s.length - 1, by simp [bs]; omega⟩
          let i : Fin ((bs ++ [k, 1])[or]) := ⟨0, by
            have hlen : bs.length = s.length - 2 := by
              simp [bs, List.length_take]
            have ho : (↑or : ℕ) = s.length - 1 := rfl
            have hle : bs.length ≤ (↑or : ℕ) := by omega
            have hidx : (↑or : ℕ) = bs.length + 1 := by omega
            have h : (bs ++ [k, 1])[or] = 1 := by
              show (bs ++ [k, 1])[(↑or : ℕ)] = 1
              simp [hidx, List.getElem_append_right]
            rw [h]; exact zero_lt_one⟩
          have hp : (bs ++ [k, 1]).eraseIdx (s.length - 1) =
              Tensor.matmul_shape s [n'] := by
            unfold Tensor.matmul_shape
            rw [dif_neg (by simp [s]), dif_neg (by simp), dif_neg (by simp [s]),
              dif_pos (by simp)]
            simp [bs, k]
            rw [List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by simp [s])]
            simp [List.EraseIdx.eq.Append_Drop_Add_1]
            simp [show s.length - 1 - (s.length - 2) = 1 by omega]
            simp [show s.length - 2 + 1 = s.length - 1 by omega]
            rw [List.DropLast.eq.Take_SubLength_1]
          have hz : cast (congrArg (Tensor α) hp) ((Xr.bmm Yt).select or i) = 0 :=
            (congrArg (fun Z => cast (congrArg (Tensor α) hp) (Z.select or i)) hb).trans
              ((congrArg (fun t => cast (congrArg (Tensor α) hp) t)
                  (Tensor.Select0.eq.Zero (o := or) i)).trans
                (Tensor.EqCast_0'0.of.Eq hp))
          convert hz
          · simp (config := { zeta := true }) only [Yt, bs]; rfl

        | cons n2 kk0 =>
          let s : List ℕ := n :: a :: b
          let s' : List ℕ := n' :: n2 :: kk0
          have h2 : 2 ≤ s.length := by
            change 2 ≤ (n :: a :: b).length
            simp
          have h2' : 2 ≤ s'.length := by
            change 2 ≤ (n' :: n2 :: kk0).length
            simp
          show Tensor.einsum X (0 : Tensor α s') = _
          unfold Tensor.einsum
          rw [dif_neg (by simp), dif_neg (by simp [s']), dif_neg (by simp),
            dif_neg (by simp [s'])]
          simp (config := { zeta := true }) only []
          let bs := s.take (s.length - 2)
          let bs' := s'.take (s'.length - 2)
          let m := s[s.length - 2]
          let nn := s[s.length - 1]
          let n2 := s'[s'.length - 2]
          let kk := s'[s'.length - 1]
          have hs1 : s' = bs' ++ [n2, kk] := by
            rwa [List.EqAppendTake__ListGet.of.GeLength_2]
          let d : Fin (bs' ++ [n2, kk]).length := ⟨bs'.length, by grind⟩
          have hs2 :
              (bs' ++ [n2, kk]).set d (nn ⊔ n2) = bs' ++ [nn ⊔ n2, kk] := by
            rw [List.SetAppend.eq.Append_Set.of.LeLength (Nat.le_refl _)
                [n2, kk] (nn ⊔ n2)]
            have hsub : (bs'.length - bs'.length) = 0 := by omega
            rw [hsub, List.Set_0.eq.Cons_Tail.of.GtLength_0 (by simp)]
            simp
          let X0 : Tensor α (bs ++ [m, nn]) :=
            cast (by rwa [List.EqAppendTake__ListGet.of.GeLength_2]) X
          let Xr : Tensor α (bs ++ [m, nn ⊔ n2]) :=
            cast (congrArg (Tensor α) (by simp))
              (X0.resize ⟨bs.length + 1, by grind⟩ (nn ⊔ n2))
          let Yt : Tensor α (bs' ++ [nn ⊔ n2, kk]) :=
            cast (congrArg (Tensor α) hs2)
              ((cast (congrArg (Tensor α) hs1) (0 : Tensor α s')).resize
                d (nn ⊔ n2))
          have hY : Yt = 0 :=
            Tensor.Cast_ResizeCast_0.eq.Zero d (nn ⊔ n2)
              (congrArg (Tensor α) hs1) hs1
              (congrArg (Tensor α) hs2) hs2
          have htd : Xr.tensordot Yt = 0 :=
            (congrArg (fun Y => Xr.tensordot Y) hY).trans (Tensor.EqTensordot_0'0 Xr)
          exact (congrArg (fun Z => cast _ Z) htd).trans
            (Tensor.EqCast_0'0.of.Eq (by rfl))



-- created on 2026-09-10
