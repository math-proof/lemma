import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.SetAppend.eq.Append_Set.of.GtLength
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.GetMatmul.as.MatmulGetS.of.Get_0.Length.GtLength_0
import Lemma.Tensor.MapBmm.eq.BmmMapS.of.All_Eq_Add.All_Eq_Mul
import Lemma.Tensor.MapCast.as.Map.of.Eq
import Lemma.Tensor.Matmul.as.Bmm
import Lemma.Tensor.Matmul.as.MatmulResizeS.of.Length.GtLength_0
import Lemma.Tensor.ResizeMap.eq.MapResize
import Lemma.Tensor.SEqMapS.of.SEq
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq
open Bool List Tensor
set_option maxHeartbeats 1000000


/-- Equal-length-batch `matmul` commutes with a pointwise map `f`. -/
@[main, comm]
private lemma main
  [Mul α] [AddCommMonoid α]
  [Mul β] [AddCancelCommMonoid β]
  {f : α → β}
  {s s' : List ℕ}
-- given
  (h_mul : ∀ a b, f (a * b) = f a * f b)
  (h_add : ∀ a b, f (a + b) = f a + f b)
  (hlen : s.length = s'.length)
  (A : Tensor α (s ++ [m, t]))
  (C : Tensor α (s' ++ [t, k])) :
-- imply
  (A.matmul C hlen).map f = (A.map f).matmul (C.map f) hlen := by
-- proof
  have h0 : f 0 = 0 := by
    have h := h_add 0 0
    simpa using h
  let F {s} (X : Tensor α s) : Tensor β s := X.map f
  have h_resize {s : List ℕ} (X : Tensor α s) (dim : Fin s.length) (n : ℕ) :
      (F X).resize dim n = F (X.resize dim n) := by
    simp only [F]
    apply ResizeMap.eq.MapResize h0
  induction s generalizing s' m t k with
  | nil =>
    match s' with
    | [] =>
      have hL := Matmul.as.Bmm (F A) (F C)
      have hR := Matmul.as.Bmm A C
      apply Bool.Eq.of.SEq
      refine (SEqMapS.of.SEq hR f).trans ?_
      refine (Bool.SEq.of.Eq
        (MapBmm.eq.BmmMapS.of.All_Eq_Add.All_Eq_Mul h_mul h_add
          (A : Tensor α ([] ++ [m, t]))
          (C : Tensor α ([] ++ [t, k])))).trans
        hL.symm
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
      let Afr : Tensor β ((n ⊔ n' :: s) ++ [m, t]) :=
        cast (congrArg (Tensor β) hcastA) ((F A).resize ⟨0, by grind⟩ (n ⊔ n'))
      let Cr : Tensor α ((n ⊔ n' :: s') ++ [t, k]) :=
        cast (congrArg (Tensor α) hcastC) (C.resize ⟨0, by grind⟩ (n ⊔ n'))
      let Crf : Tensor β ((n ⊔ n' :: s') ++ [t, k]) :=
        cast (congrArg (Tensor β) hcastC) ((F C).resize ⟨0, by grind⟩ (n ⊔ n'))
      have hAfr : Afr = F Ar := by
        simp only [Afr, Ar, F]
        rw [h_resize]
        simp only [F]
        exact Cast_Map.eq.MapCast.of.Eq hcastA (A.resize ⟨0, by grind⟩ (n ⊔ n')) f
      have hCrf : Crf = F Cr := by
        simp only [Crf, Cr, F]
        rw [h_resize]
        simp only [F]
        exact Cast_Map.eq.MapCast.of.Eq hcastC (C.resize ⟨0, by grind⟩ (n ⊔ n')) f
      have hL :=
        Matmul.as.MatmulResizeS.of.Length.GtLength_0 (s := n :: s) (s' := n' :: s')
          (by simp) hlen (F A) (F C)
      have hR :=
        Matmul.as.MatmulResizeS.of.Length.GtLength_0 (s := n :: s) (s' := n' :: s')
          (by simp) hlen A C
      have hmat : F (Ar.matmul Cr (by simpa using hlen')) =
          Afr.matmul Crf (by simpa using hlen') := by
        rw [hAfr, hCrf]
        have hshape :
            broadcast_shape (n ⊔ n' :: s) (n ⊔ n' :: s') ++ [m, k] =
              (n ⊔ n') :: (broadcast_shape s s' ++ [m, k]) := by
          simp [broadcast_shape]; split_ifs <;> simp_all
        let L : Tensor α ((n ⊔ n') :: (broadcast_shape s s' ++ [m, k])) :=
          cast (congrArg (Tensor α) hshape)
            (Ar.matmul Cr (by simpa using hlen'))
        let R : Tensor β ((n ⊔ n') :: (broadcast_shape s s' ++ [m, k])) :=
          cast (congrArg (Tensor β) hshape)
            ((F Ar).matmul (F Cr) (by simpa using hlen'))
        have hLR : F L = R := by
          apply Tensor.Eq.of.All_EqGetS
          intro i
          have hFL : (F L)[i] = F (L[i]) := by
            simp only [F]
            exact GetMap.eq.MapGet.fin L f i
          rw [hFL]
          apply Bool.Eq.of.SEq
          have hlenA : (n ⊔ n' :: s).length = (n ⊔ n' :: s').length := by
            simpa using hlen'
          have hgetL :=
            GetMatmul.as.MatmulGetS.of.Get_0.Length.GtLength_0
              (s := n ⊔ n' :: s) (s' := n ⊔ n' :: s')
              (by simp) hlenA (by rfl) Ar Cr i
          have hgetR :=
            GetMatmul.as.MatmulGetS.of.Get_0.Length.GtLength_0
              (s := n ⊔ n' :: s) (s' := n ⊔ n' :: s')
              (by simp) hlenA (by rfl) (F Ar) (F Cr) i
          have hCL :=
            GetCast.as.Get.of.Eq.GtLength_0.right.fin (by simp) hshape
              (Ar.matmul Cr (by simpa using hlen')) i
          have hCR :=
            GetCast.as.Get.of.Eq.GtLength_0.right.fin (by simp) hshape
              ((F Ar).matmul (F Cr) (by simpa using hlen')) i
          have hAi : (F Ar)[i] = F (Ar[i]) := by
            simp only [F]
            exact GetMap.eq.MapGet.fin Ar f i
          have hCi : (F Cr)[i] = F (Cr[i]) := by
            simp only [F]
            exact GetMap.eq.MapGet.fin Cr f i
          have ih' := ih hlen' (Ar[i]) (Cr[i])
          have hXA : (n ⊔ n' :: s) ++ [m, t] = ((n ⊔ n' :: s)[0] :: (n ⊔ n' :: s).tail) ++ [m, t] := by
            simp
          have hYA : (n ⊔ n' :: s') ++ [t, k] = ((n ⊔ n' :: s')[0] :: (n ⊔ n' :: s').tail) ++ [t, k] := by
            simp
          refine (SEqMapS.of.SEq hCL f).trans (SEqMapS.of.SEq hgetL f) |>.trans (Bool.SEq.of.Eq ih') |>.trans ?_ |>.trans
            hgetR.symm |>.trans hCR.symm
          exact
            (SEqMatmulS.of.SEq.SEq (by simpa using hlen')
              ((GetCast.as.Get.of.Eq.GtLength_0.right.fin
                  (by simp) hXA (F Ar) i).trans (Bool.SEq.of.Eq hAi)).symm
              ((GetCast.as.Get.of.Eq.GtLength_0.right.fin
                  (by simp) hYA (F Cr) i).trans (Bool.SEq.of.Eq hCi)).symm)
        apply Bool.Eq.of.SEq
        have hcastL := Bool.SEqCast.of.Eq hshape (Ar.matmul Cr (by simpa using hlen'))
        have hcastR := Bool.SEqCast.of.Eq hshape ((F Ar).matmul (F Cr) (by simpa using hlen'))
        exact (SEqMapS.of.SEq hcastL.symm f).trans (Bool.SEq.of.Eq hLR) |>.trans hcastR
      apply Bool.Eq.of.SEq
      refine (SEqMapS.of.SEq hR f).trans ?_
      exact (Bool.SEq.of.Eq hmat).trans hL.symm


-- created on 2026-08-17
