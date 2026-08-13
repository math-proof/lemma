import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Bool.SEqUFnS.of.SEq
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.List.SetAppend.eq.Append_Set.of.GtLength
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.Tensor.BmmDiv.eq.DivBmm
import Lemma.Tensor.CastDiv.eq.DivCast.of.Eq
import Lemma.Tensor.Einsum.as.Tensordot.of.GeLength_2.GeLength_2
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetDiv.eq.DivGet
import Lemma.Tensor.GetMatmul.as.MatmulGetS.of.Get_0.Length.GtLength_0
import Lemma.Tensor.Matmul.as.Bmm
import Lemma.Tensor.Matmul.as.MatmulResizeS.of.Length.GtLength_0
import Lemma.Tensor.ReshapeDiv.eq.DivReshape.of.Dvd
import Lemma.Tensor.ResizeDiv.eq.DivResize
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq
import Lemma.Tensor.SEqTensordotS.of.SEq.SEq.Eq.Eq
import Lemma.Tensor.Tensordot.as.Matmul.of.GeLengthS
import Lemma.Tensor.Tensordot.as.Matmul.of.LtLengthS
import Lemma.Tensor.Tensordot.eq.Matmul.of.Length
open Bool List Tensor
set_option maxHeartbeats 1000000


/-- Equal-length-batch `matmul` distributes over scalar division. -/
private lemma matmul_div_eq_len
  [Semifield α]
  {s s' : List ℕ}
-- given
  (hlen : s.length = s'.length)
  (A : Tensor α (s ++ [m, t]))
  (C : Tensor α (s' ++ [t, k]))
  (B : Tensor α []) :
-- imply
  (A / B).matmul C hlen = A.matmul C hlen / B := by
-- proof
  induction s generalizing s' m t k with
  | nil =>
    match s' with
    | [] =>
      have hL := Matmul.as.Bmm (A / B) C
      have hR := Matmul.as.Bmm A C
      apply Bool.Eq.of.SEq
      exact hL.trans (Bool.SEq.of.Eq (BmmDiv.eq.DivBmm A C B)) |>.trans (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
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
      let Adr : Tensor α ((n ⊔ n' :: s) ++ [m, t]) :=
        cast (congrArg (Tensor α) hcastA) ((A / B).resize ⟨0, by grind⟩ (n ⊔ n'))
      let Cr : Tensor α ((n ⊔ n' :: s') ++ [t, k]) :=
        cast (congrArg (Tensor α) hcastC) (C.resize ⟨0, by grind⟩ (n ⊔ n'))
      have hAdr : Adr = Ar / B := by
        simp only [Adr, Ar]
        rw [ResizeDiv.eq.DivResize A B ⟨0, by grind⟩ (n ⊔ n')]
        exact CastDiv.eq.DivCast.of.Eq hcastA _ B
      have hL :=
        Matmul.as.MatmulResizeS.of.Length.GtLength_0 (s := n :: s) (s' := n' :: s')
          (by simp) hlen (A / B) C
      have hR :=
        Matmul.as.MatmulResizeS.of.Length.GtLength_0 (s := n :: s) (s' := n' :: s')
          (by simp) hlen A C
      have hmat : Adr.matmul Cr (by simpa using hlen') =
          Ar.matmul Cr (by simpa using hlen') / B := by
        rw [hAdr]
        have hshape :
            broadcast_shape (n ⊔ n' :: s) (n ⊔ n' :: s') ++ [m, k] =
              (n ⊔ n') :: (broadcast_shape s s' ++ [m, k]) := by
          simp [broadcast_shape]; split_ifs <;> simp_all
        let L : Tensor α ((n ⊔ n') :: (broadcast_shape s s' ++ [m, k])) :=
          cast (congrArg (Tensor α) hshape)
            ((Ar / B).matmul Cr (by simpa using hlen'))
        let R : Tensor α ((n ⊔ n') :: (broadcast_shape s s' ++ [m, k])) :=
          cast (congrArg (Tensor α) hshape)
            (Ar.matmul Cr (by simpa using hlen'))
        have hLR : L = R / B := by
          apply Tensor.Eq.of.All_EqGetS
          intro i
          rw [Tensor.GetDiv.eq.DivGet]
          apply Bool.Eq.of.SEq
          have hlenA : (n ⊔ n' :: s).length = (n ⊔ n' :: s').length := by
            simpa using hlen'
          have hgetL :=
            GetMatmul.as.MatmulGetS.of.Get_0.Length.GtLength_0
              (s := n ⊔ n' :: s) (s' := n ⊔ n' :: s')
              (by simp) hlenA (by rfl) (Ar / B) Cr i
          have hgetR :=
            GetMatmul.as.MatmulGetS.of.Get_0.Length.GtLength_0
              (s := n ⊔ n' :: s) (s' := n ⊔ n' :: s')
              (by simp) hlenA (by rfl) Ar Cr i
          have hCL :=
            GetCast.as.Get.of.Eq.GtLength_0.right.fin (by simp) hshape
              ((Ar / B).matmul Cr (by simpa using hlen')) i
          have hCR :=
            GetCast.as.Get.of.Eq.GtLength_0.right.fin (by simp) hshape
              (Ar.matmul Cr (by simpa using hlen')) i
          have hAi : (Ar / B)[i] = Ar[i] / B := Tensor.GetDiv.eq.DivGet Ar B i
          have ih' := ih hlen' (Ar[i]) (Cr[i])
          have hXA :
              (n ⊔ n' :: s) ++ [m, t] =
                ((n ⊔ n' :: s)[0] :: (n ⊔ n' :: s).tail) ++ [m, t] := by
            simp
          have hYA :
              (n ⊔ n' :: s') ++ [t, k] =
                ((n ⊔ n' :: s')[0] :: (n ⊔ n' :: s').tail) ++ [t, k] := by
            simp
          refine hCL.trans hgetL |>.trans ?_ |>.trans
            (Bool.SEqUFnS.of.SEq hgetR.symm
              (fun (t : Tensor α _) => (t / B : Tensor α _))) |>.trans
            (Bool.SEqUFnS.of.SEq hCR
              (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
          refine
            (SEqMatmulS.of.SEq.SEq (by simpa using hlen')
              ((GetCast.as.Get.of.Eq.GtLength_0.right.fin
                  (by simp) hXA (Ar / B) i).trans (Bool.SEq.of.Eq hAi))
              (GetCast.as.Get.of.Eq.GtLength_0.right.fin
                  (by simp) hYA Cr i)).trans
              (Bool.SEq.of.Eq ih')
        apply Bool.Eq.of.SEq
        refine (Bool.SEqCast.of.Eq hshape
            ((Ar / B).matmul Cr (by simpa using hlen'))).symm.trans ?_
        exact (Bool.SEq.of.Eq hLR).trans
          (Bool.SEqUFnS.of.SEq (Bool.SEqCast.of.Eq hshape
              (Ar.matmul Cr (by simpa using hlen')))
            (fun (t : Tensor α _) => (t / B : Tensor α _)))
      apply Bool.Eq.of.SEq
      refine hL.trans ?_
      have hmid := Bool.SEq.of.Eq hmat
      simpa [Adr, Ar, Cr] using hmid.trans (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


/-- Identical-batch `matmul` distributes over scalar division. -/
private lemma matmul_div
  [Semifield α]
  {s : List ℕ}
-- given
  (A : Tensor α (s ++ [m, t]))
  (C : Tensor α (s ++ [t, k]))
  (B : Tensor α []) :
-- imply
  (A / B).matmul C (by rfl) = A.matmul C (by rfl) / B :=
-- proof
  matmul_div_eq_len (by rfl) A C B


/-- Identical-batch `tensordot` distributes over scalar division. -/
private lemma tensordot_div_same
  [Semifield α]
  {s : List ℕ}
-- given
  (A : Tensor α (s ++ [m, n]))
  (C : Tensor α (s ++ [n, k]))
  (B : Tensor α []) :
-- imply
  (A / B).tensordot C = A.tensordot C / B := by
-- proof
  have h1 := Tensordot.eq.Matmul.of.Length (by rfl) (A / B) C
  have h2 := Tensordot.eq.Matmul.of.Length (by rfl) A C
  rw [h1, h2]
  exact matmul_div A C B


/-- Both ranks ≥ 2 with equal batch prefixes. -/
private lemma both_ge_2
  [Semifield α]
-- given
  (hs : s.length ≥ 2)
  (hs' : s'.length ≥ 2)
  (hb : s.take (s.length - 2) = s'.take (s'.length - 2))
  (A : Tensor α s)
  (C : Tensor α s')
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  have hE := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' A C
  have hEd := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' (A / B) C
  apply Bool.Eq.of.SEq
  let batch := s.take (s.length - 2)
  let batch' := s'.take (s'.length - 2)
  let m := s[s.length - 2]
  let n := s[s.length - 1]
  let n' := s'[s'.length - 2]
  let k := s'[s'.length - 1]
  let K := n ⊔ n'
  let X0 : Tensor α (batch ++ [m, n]) :=
    cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
  let Xd0 : Tensor α (batch ++ [m, n]) :=
    cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) (A / B)
  have hXd0 : Xd0 = X0 / B :=
    CastDiv.eq.DivCast.of.Eq (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
  let X : Tensor α (batch ++ [m, K]) :=
    cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ K)
  let Xd : Tensor α (batch ++ [m, K]) :=
    cast (by simp) (Xd0.resize ⟨batch.length + 1, by grind⟩ K)
  have hXd : Xd = X / B := by
    simp only [Xd, X, hXd0]
    rw [ResizeDiv.eq.DivResize X0 B ⟨batch.length + 1, by grind⟩ K]
    exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
  let Y0 : Tensor α (batch' ++ [n', k]) :=
    cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm) C
  let Y' : Tensor α (batch' ++ [K, k]) :=
    cast (by simp) (Y0.resize ⟨batch'.length, by grind⟩ K)
  have hbY : batch' ++ [K, k] = batch ++ [K, k] := by
    simp only [batch, batch']; rw [hb]
  let Y : Tensor α (batch ++ [K, k]) :=
    cast (congrArg (Tensor α) hbY) Y'
  have hY : Y' ≃ Y := (Bool.SEqCast.of.Eq hbY Y').symm
  have htd : Xd.tensordot Y = X.tensordot Y / B := by
    rw [hXd]; exact tensordot_div_same X Y B
  have htd' : Xd.tensordot Y' = X.tensordot Y' / B := by
    apply Bool.Eq.of.SEq
    have h1 :=
      SEqTensordotS.of.SEq.SEq.Eq.Eq (by rfl) (by rfl) (by rfl : Xd ≃ Xd) hY
    have h2 :=
      SEqTensordotS.of.SEq.SEq.Eq.Eq (by rfl) (by rfl) (by rfl : X ≃ X) hY
    exact h1.trans (Bool.SEq.of.Eq htd) |>.trans
      (Bool.SEqUFnS.of.SEq h2.symm (fun (t : Tensor α _) => (t / B : Tensor α _)))
  have hL : (A / B).einsum C ≃ Xd.tensordot Y' := by
    refine hEd.trans ?_
    simp only [Xd, Xd0, Y', Y0, batch, batch', m, n, n', k, K]
    rfl
  have hR : A.einsum C ≃ X.tensordot Y' := by
    refine hE.trans ?_
    simp only [X, X0, Y', Y0, batch, batch', m, n, n', k, K]
    rfl
  exact hL.trans (Bool.SEq.of.Eq htd') |>.trans (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


private lemma tensordot_div
  [Semifield α]
  {s s' : List ℕ}
-- given
  (A : Tensor α (s ++ [m, n]))
  (C : Tensor α (s' ++ [n, k]))
  (B : Tensor α []) :
-- imply
  (A / B).tensordot C = A.tensordot C / B := by
-- proof
  if hlt : s.length < s'.length then
    have hL := Tensordot.as.Matmul.of.LtLengthS hlt (A / B) C
    have hR := Tensordot.as.Matmul.of.LtLengthS hlt A C
    let sR := s'.take (s'.length - s.length) ++ s ++ [m, n]
    have hdvd : (s ++ [m, n]).prod ∣ sR.prod := by grind
    have hmat := matmul_div_eq_len (by grind) (A.reshape sR hdvd) C B
    apply Bool.Eq.of.SEq
    refine hL.trans ?_
    convert (Bool.SEq.of.Eq (by
      change ((A / B).reshape sR hdvd).matmul C (by grind) = _
      rwa [ReshapeDiv.eq.DivReshape.of.Dvd hdvd])).trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else if hgt : s.length > s'.length then
    have hge : s.length ≥ s'.length := Nat.le_of_lt hgt
    have hL := Tensordot.as.Matmul.of.GeLengthS hge (A / B) C
    have hR := Tensordot.as.Matmul.of.GeLengthS hge A C
    let sL := s.take (s.length - s'.length) ++ s' ++ [n, k]
    have hdvd : (s' ++ [n, k]).prod ∣ sL.prod := by
      have hsL : sL = s.take (s.length - s'.length) ++ (s' ++ [n, k]) := by grind
      rw [hsL]
      conv_rhs => rw [List.prod_append]
      exact Nat.dvd_mul_left _ _
    have hmat' := matmul_div_eq_len (by grind) A (C.reshape sL hdvd) B
    apply Bool.Eq.of.SEq
    refine hL.trans ?_
    convert (Bool.SEq.of.Eq hmat').trans (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else
    have hlen := Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
    have h1 := Tensordot.eq.Matmul.of.Length hlen (A / B) C
    have h2 := Tensordot.eq.Matmul.of.Length hlen A C
    rw [h1, h2]
    apply matmul_div_eq_len hlen


@[main]
private lemma main
  [Semifield α]
-- given
  (hs : s.length ≥ 2)
  (hs' : s'.length ≥ 2)
  (A : Tensor α s)
  (C : Tensor α s')
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  if hb : s.take (s.length - 2) = s'.take (s'.length - 2) then
    apply both_ge_2 hs hs' hb
  else
    simp only [Dot.dot]
    have hE := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' A C
    have hEd := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' (A / B) C
    apply Bool.Eq.of.SEq
    let batch := s.take (s.length - 2)
    let batch' := s'.take (s'.length - 2)
    let m := s[s.length - 2]
    let n := s[s.length - 1]
    let n' := s'[s'.length - 2]
    let k := s'[s'.length - 1]
    let K := n ⊔ n'
    let X0 : Tensor α (batch ++ [m, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
    let Xd0 : Tensor α (batch ++ [m, n]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) (A / B)
    have hXd0 : Xd0 = X0 / B :=
      CastDiv.eq.DivCast.of.Eq (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
    let X : Tensor α (batch ++ [m, K]) :=
      cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ K)
    let Xd : Tensor α (batch ++ [m, K]) :=
      cast (by simp) (Xd0.resize ⟨batch.length + 1, by grind⟩ K)
    have hXd : Xd = X / B := by
      simp only [Xd, X, hXd0]
      rw [ResizeDiv.eq.DivResize X0 B ⟨batch.length + 1, by grind⟩ K]
      exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
    let Y0 : Tensor α (batch' ++ [n', k]) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm) C
    let Y' : Tensor α (batch' ++ [K, k]) :=
      cast (by simp) (Y0.resize ⟨batch'.length, by grind⟩ K)
    have htd : Xd.tensordot Y' = X.tensordot Y' / B := by
      rw [hXd]
      apply tensordot_div
    have hL : (A / B).einsum C ≃ Xd.tensordot Y' := by
      refine hEd.trans ?_
      simp only [Xd, Xd0, Y', Y0, batch, batch', m, n, n', k, K]
      rfl
    have hR : A.einsum C ≃ X.tensordot Y' := by
      refine hE.trans ?_
      simp only [X, X0, Y', Y0, batch, batch', m, n, n', k, K]
      rfl
    apply (hL.trans (Bool.SEq.of.Eq htd)).trans
    symm
    apply Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))


-- created on 2026-08-13
