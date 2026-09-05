import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Bool.SEqUFnS.of.SEq
import Lemma.List.SetAppend.eq.Append_Set.of.GtLength
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.Tensor.BmmBFn.eq.BFnBmm
import Lemma.Tensor.MapCast.as.MapBFn.of.Eq
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.GetMatmul.as.MatmulGetS.of.Get_0.Length.GtLength_0
import Lemma.Tensor.Matmul.as.Bmm
import Lemma.Tensor.Matmul.as.MatmulResizeS.of.Length.GtLength_0
import Lemma.Tensor.ResizeBFn.eq.BFnResize
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq
open Bool List Tensor
set_option maxHeartbeats 1000000


/-- Equal-length-batch `matmul` commutes with a pointwise scalar binary operator `f`. -/
@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
  {f : α → α → α}
  {s s' : List ℕ}
-- given
  (h_mul : ∀ {s : List ℕ} (X C : Tensor α s) (B : Tensor α []), X.map (f · B.data[0]) * C = (X * C).map (f · B.data[0]))
  (h_sum : ∀ {s : List ℕ} (X : Tensor α s) (B : Tensor α []) (dim : ℕ), (X.map (f · B.data[0])).sum dim = (X.sum dim).map (f · B.data[0]))
  (h0 : ∀ b : α, f 0 b = 0)
  (hlen : s.length = s'.length)
  (A : Tensor α (s ++ [m, t]))
  (C : Tensor α (s' ++ [t, k]))
  (B : Tensor α []) :
-- imply
  (A.map (f · B.data[0])).matmul C hlen = (A.matmul C hlen).map (f · B.data[0]) := by
-- proof
  let F {s} (X : Tensor α s) : Tensor α s := X.map (f · B.data[0])
  have h_resize {s : List ℕ} (X : Tensor α s) (dim : Fin s.length) (n : ℕ) : (F X).resize dim n = F (X.resize dim n) := by
    simp only [F]
    apply ResizeBFn.eq.BFnResize h0 X B dim n
  induction s generalizing s' m t k with
  | nil =>
    match s' with
    | [] =>
      have hL := Matmul.as.Bmm (F A) C
      have hR := Matmul.as.Bmm A C
      apply Bool.Eq.of.SEq
      exact hL.trans (Bool.SEq.of.Eq (BmmBFn.eq.BFnBmm (f := f) h_mul h_sum A C B)) |>.trans
        (Bool.SEqUFnS.of.SEq hR (F ·)).symm
    | _ :: _ =>
      simp at hlen
  | cons n s ih =>
    match s' with
    | [] =>
      simp at hlen
    | n' :: s' =>
      have hlen' : s.length = s'.length := by simpa using hlen
      have hcastA :
          ((n :: s) ++ [m, t]).set 0 (n ⊔ n') = (n ⊔ n' :: s) ++ [m, t] := by
        rw [List.SetAppend.eq.Append_Set.of.GtLength (by simp)]
        simp [List.Set_0.eq.Cons_Tail.of.GtLength_0]
      have hcastC :
          ((n' :: s') ++ [t, k]).set 0 (n ⊔ n') = (n ⊔ n' :: s') ++ [t, k] := by
        rw [List.SetAppend.eq.Append_Set.of.GtLength (by simp)]
        simp [List.Set_0.eq.Cons_Tail.of.GtLength_0]
      let Ar : Tensor α ((n ⊔ n' :: s) ++ [m, t]) :=
        cast (congrArg (Tensor α) hcastA) (A.resize ⟨0, by grind⟩ (n ⊔ n'))
      let Afr : Tensor α ((n ⊔ n' :: s) ++ [m, t]) :=
        cast (congrArg (Tensor α) hcastA) ((F A).resize ⟨0, by grind⟩ (n ⊔ n'))
      let Cr : Tensor α ((n ⊔ n' :: s') ++ [t, k]) :=
        cast (congrArg (Tensor α) hcastC) (C.resize ⟨0, by grind⟩ (n ⊔ n'))
      have hAfr : Afr = F Ar := by
        simp only [Afr, Ar]
        rw [h_resize]
        exact Cast_MapBFn.eq.MapCast.of.Eq (f := f) hcastA _ B
      have hL :=
        Matmul.as.MatmulResizeS.of.Length.GtLength_0 (s := n :: s) (s' := n' :: s')
          (by simp) hlen (F A) C
      have hR :=
        Matmul.as.MatmulResizeS.of.Length.GtLength_0 (s := n :: s) (s' := n' :: s')
          (by simp) hlen A C
      have hmat : Afr.matmul Cr (by simpa using hlen') =
          F (Ar.matmul Cr (by simpa using hlen')) := by
        rw [hAfr]
        have hshape :
            broadcast_shape (n ⊔ n' :: s) (n ⊔ n' :: s') ++ [m, k] =
              (n ⊔ n') :: (broadcast_shape s s' ++ [m, k]) := by
          simp [broadcast_shape]; split_ifs <;> simp_all
        let L : Tensor α ((n ⊔ n') :: (broadcast_shape s s' ++ [m, k])) :=
          cast (congrArg (Tensor α) hshape)
            ((F Ar).matmul Cr (by simpa using hlen'))
        let R : Tensor α ((n ⊔ n') :: (broadcast_shape s s' ++ [m, k])) :=
          cast (congrArg (Tensor α) hshape)
            (Ar.matmul Cr (by simpa using hlen'))
        have hLR : L = F R := by
          apply Tensor.Eq.of.All_EqGetS
          intro i
          have hFR : (F R)[i] = F R[i] := by
            simp only [F]
            exact GetMap.eq.MapGet.fin R (f · B.data[0]) i
          rw [hFR]
          apply Bool.Eq.of.SEq
          have hlenA : (n ⊔ n' :: s).length = (n ⊔ n' :: s').length := by
            simpa using hlen'
          have hgetL :=
            GetMatmul.as.MatmulGetS.of.Get_0.Length.GtLength_0
              (s := n ⊔ n' :: s) (s' := n ⊔ n' :: s')
              (by simp) hlenA (by rfl) (F Ar) Cr i
          have hgetR :=
            GetMatmul.as.MatmulGetS.of.Get_0.Length.GtLength_0
              (s := n ⊔ n' :: s) (s' := n ⊔ n' :: s')
              (by simp) hlenA (by rfl) Ar Cr i
          have hCL :=
            GetCast.as.Get.of.Eq.GtLength_0.right.fin (by simp) hshape
              ((F Ar).matmul Cr (by simpa using hlen')) i
          have hCR :=
            GetCast.as.Get.of.Eq.GtLength_0.right.fin (by simp) hshape
              (Ar.matmul Cr (by simpa using hlen')) i
          have hAi : (F Ar)[i] = F Ar[i] := by
            simp only [F]
            exact GetMap.eq.MapGet.fin Ar (f · B.data[0]) i
          have ih' := ih hlen' Ar[i] Cr[i]
          have hXA : (n ⊔ n' :: s) ++ [m, t] = ((n ⊔ n' :: s)[0] :: (n ⊔ n' :: s).tail) ++ [m, t] := by
            simp
          have hYA : (n ⊔ n' :: s') ++ [t, k] = ((n ⊔ n' :: s')[0] :: (n ⊔ n' :: s').tail) ++ [t, k] := by
            simp
          refine hCL.trans hgetL |>.trans ?_ |>.trans (Bool.SEqUFnS.of.SEq hgetR.symm (F ·)) |>.trans (Bool.SEqUFnS.of.SEq hCR (F ·)).symm
          refine
            (SEqMatmulS.of.SEq.SEq (by simpa using hlen')
              ((GetCast.as.Get.of.Eq.GtLength_0.right.fin
                  (by simp) hXA (F Ar) i).trans (Bool.SEq.of.Eq hAi))
              (GetCast.as.Get.of.Eq.GtLength_0.right.fin
                  (by simp) hYA Cr i)).trans
              (Bool.SEq.of.Eq ih')
        apply Bool.Eq.of.SEq
        refine (Bool.SEqCast.of.Eq hshape ((F Ar).matmul Cr (by simpa using hlen'))).symm.trans ?_
        exact (Bool.SEq.of.Eq hLR).trans (Bool.SEqUFnS.of.SEq (Bool.SEqCast.of.Eq hshape (Ar.matmul Cr (by simpa using hlen'))) (F ·))
      apply Bool.Eq.of.SEq
      refine hL.trans ?_
      have hmid := Bool.SEq.of.Eq hmat
      simpa [Afr, Ar, Cr, F] using hmid.trans (Bool.SEqUFnS.of.SEq hR (F ·)).symm


-- created on 2026-08-15
