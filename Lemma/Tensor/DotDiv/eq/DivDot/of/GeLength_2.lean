import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqUFnS.of.SEq
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.Tensor.BmmDiv.eq.DivBmm
import Lemma.Tensor.CastDiv.eq.DivCast.of.Eq
import Lemma.Tensor.Einsum.as.SelectBmm.of.Eq_Get_SubLength.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2
import Lemma.Tensor.ReshapeDiv.eq.DivReshape.of.Dvd
import Lemma.Tensor.ResizeDiv.eq.DivResize
import Lemma.Tensor.SelectDiv.eq.DivSelect
open Bool List Tensor


@[main]
private lemma main
  [Semifield α]
-- given
  (hs' : s'.length ≥ 2)
  (A : Tensor α [n])
  (C : Tensor α s')
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  if h_eq : n = s'[s'.length - 2] then
    have hE := Einsum.as.SelectBmm.of.Eq_Get_SubLength.GeLength_2 hs' h_eq A C
    have hEd := Einsum.as.SelectBmm.of.Eq_Get_SubLength.GeLength_2 hs' h_eq (A / B) C
    apply Bool.Eq.of.SEq
    let batch := s'.take (s'.length - 2)
    let k := s'[s'.length - 1]
    let Y' : Tensor α (batch ++ [n, k]) :=
      cast (congrArg (Tensor α) (by
        simp only [batch, k]
        rw [h_eq]
        exact (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm)) C
    let X' := A.reshape (batch ++ [1, n]) (by simp)
    let Xd := (A / B).reshape (batch ++ [1, n]) (by simp)
    have hbmm : Xd.bmm Y' = X'.bmm Y' / B := by
      simp [Xd]
      rw [ReshapeDiv.eq.DivReshape.of.Dvd]
      apply BmmDiv.eq.DivBmm
    have hsel : (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ = (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]
      apply SelectDiv.eq.DivSelect
    have hL : (A / B).einsum C ≃ (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xd, Y', batch, k]
      rfl
    have hR : A.einsum C ≃ (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X', Y', batch, k]
      rfl
    exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else if hgt : n > s'[s'.length - 2] then
    have hE := Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2 hs' hgt A C
    have hEd := Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2 hs' hgt (A / B) C
    apply Bool.Eq.of.SEq
    let batch := s'.take (s'.length - 2)
    let n₀ := s'[s'.length - 2]
    let k' := s'[s'.length - 1]
    let Y0 : Tensor α (batch ++ [n₀, k']) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm) C
    let Y' : Tensor α (batch ++ [n, k']) :=
      cast (by simp) (Y0.resize ⟨batch.length, by grind⟩ n)
    let X' := A.reshape (batch ++ [1, n]) (by simp)
    let Xd := (A / B).reshape (batch ++ [1, n]) (by simp)
    have hbmm : Xd.bmm Y' = X'.bmm Y' / B := by
      simp [Xd]
      rw [ReshapeDiv.eq.DivReshape.of.Dvd]
      apply BmmDiv.eq.DivBmm
    have hsel : (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ = (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]
      apply SelectDiv.eq.DivSelect
    have hL : (A / B).einsum C ≃ (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xd, Y', Y0, batch, n₀, k']
      rfl
    have hR : A.einsum C ≃ (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X', Y', Y0, batch, n₀, k']
      rfl
    exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else
    have hlt := Nat.lt_of_le_of_ne (le_of_not_gt hgt) h_eq
    have hE := Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2 hs' hlt A C
    have hEd := Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2 hs' hlt (A / B) C
    apply Bool.Eq.of.SEq
    let batch := s'.take (s'.length - 2)
    let n₀ := s'[s'.length - 2]
    let k' := s'[s'.length - 1]
    let Y' : Tensor α (batch ++ [n₀, k']) :=
      cast (congrArg (Tensor α) (by
        simp only [batch, n₀, k']
        exact (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm)) C
    let A_r : Tensor α [n₀] := cast (by simp) (A.resize ⟨0, by grind⟩ n₀)
    let Ad_r : Tensor α [n₀] := cast (by simp) ((A / B).resize ⟨0, by grind⟩ n₀)
    have hr : Ad_r = A_r / B := by
      simp only [Ad_r, A_r]
      rw [ResizeDiv.eq.DivResize A B ⟨0, by grind⟩ n₀]
      exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
    let X' := A_r.reshape (batch ++ [1, n₀]) (by simp)
    let Xd := Ad_r.reshape (batch ++ [1, n₀]) (by simp)
    have hx : Xd = X' / B := by
      simp only [Xd, X', hr]
      apply ReshapeDiv.eq.DivReshape.of.Dvd
    have hbmm : Xd.bmm Y' = X'.bmm Y' / B := by
      rw [hx]
      apply BmmDiv.eq.DivBmm
    have hsel : (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ = (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]
      apply SelectDiv.eq.DivSelect
    have hL : (A / B).einsum C ≃ (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xd, Y', Ad_r, batch, n₀, k']
      rfl
    have hR : A.einsum C ≃ (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X', Y', A_r, batch, n₀, k']
      rfl
    exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


@[main]
private lemma left
  [Semifield α]
-- given
  (hs : s.length ≥ 2)
  (A : Tensor α s)
  (C : Tensor α [n'])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  have hE := Einsum.as.SelectBmm.of.GeLength_2 hs A C
  have hEd := Einsum.as.SelectBmm.of.GeLength_2 hs (A / B) C
  apply Bool.Eq.of.SEq
  let batch := s.take (s.length - 2)
  let k := s[s.length - 2]
  let n := s[s.length - 1]
  let K := n ⊔ n'
  let X0 : Tensor α (batch ++ [k, n]) :=
    cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
  let Xd0 : Tensor α (batch ++ [k, n]) :=
    cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) (A / B)
  have hx0 : Xd0 = X0 / B :=
    CastDiv.eq.DivCast.of.Eq (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
  let X : Tensor α (batch ++ [k, K]) :=
    cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ K)
  let Xd : Tensor α (batch ++ [k, K]) :=
    cast (by simp) (Xd0.resize ⟨batch.length + 1, by grind⟩ K)
  have hX : Xd = X / B := by
    simp only [X, Xd, hx0]
    rw [ResizeDiv.eq.DivResize X0 B ⟨batch.length + 1, by grind⟩ K]
    exact CastDiv.eq.DivCast.of.Eq (by simp) _ B
  let Cr : Tensor α [K] := C.resize ⟨0, by grind⟩ K
  let Y' := Cr.reshape (batch ++ [K, 1]) (by simp)
  have hbmm : Xd.bmm Y' = X.bmm Y' / B := by
    rw [hX]
    apply BmmDiv.eq.DivBmm
  have hsel : (Xd.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ = (X.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ / B := by
    rw [hbmm]
    apply SelectDiv.eq.DivSelect
  have hL : (A / B).einsum C ≃ (Xd.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
    refine hEd.trans ?_
    simp only [Xd, Xd0, Y', Cr, batch, k, n, K]
    rfl
  have hR : A.einsum C ≃ (X.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
    refine hE.trans ?_
    simp only [X, X0, Y', Cr, batch, k, n, K]
    rfl
  exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans
    (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


-- created on 2026-08-13
