import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqUFnS.of.SEq
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.Tensor.BmmBFn.eq.BFnBmm
import Lemma.Tensor.MapCast.as.MapBFn.of.Eq
import Lemma.Tensor.Einsum.as.SelectBmm.of.Eq_Get_SubLength.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2
import Lemma.Tensor.ReshapeBFn.eq.BFnReshape.of.Dvd
import Lemma.Tensor.ResizeBFn.eq.BFnResize
import Lemma.Tensor.SelectBFn.eq.BFnSelect
open Bool List Tensor
set_option maxHeartbeats 1000000


/-- `dot` commutes with a pointwise scalar binary operator `f` when the right rank is ≥ 2 and the left is a vector. -/
@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
  {f : α → α → α}
-- given
  (h_mul : ∀ {s : List ℕ} (X C : Tensor α s) (B : Tensor α []), X.map (f · B.data[0]) * C = (X * C).map (f · B.data[0]))
  (h_sum : ∀ {s : List ℕ} (X : Tensor α s) (B : Tensor α []) (dim : ℕ), (X.map (f · B.data[0])).sum dim = (X.sum dim).map (f · B.data[0]))
  (h0 : ∀ b : α, f 0 b = 0)
  (hs' : s'.length ≥ 2)
  (A : Tensor α [n])
  (C : Tensor α s')
  (B : Tensor α []) :
-- imply
  (A.map (f · B.data[0])) @ C = (A @ C).map (f · B.data[0]) := by
-- proof
  let F {s} (X : Tensor α s) : Tensor α s := X.map (f · B.data[0])
  simp only [Dot.dot]
  if h_eq : n = s'[s'.length - 2] then
    have hE := Einsum.as.SelectBmm.of.Eq_Get_SubLength.GeLength_2 hs' h_eq A C
    have hEf := Einsum.as.SelectBmm.of.Eq_Get_SubLength.GeLength_2 hs' h_eq (F A) C
    apply Bool.Eq.of.SEq
    let batch := s'.take (s'.length - 2)
    let k := s'[s'.length - 1]
    let Y' : Tensor α (batch ++ [n, k]) :=
      cast (congrArg (Tensor α) (by
        simp only [batch, k]
        rw [h_eq]
        exact (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm)) C
    let X' := A.reshape (batch ++ [1, n]) (by simp)
    let Af := (F A).reshape (batch ++ [1, n]) (by simp)
    have hbmm : Af.bmm Y' = F (X'.bmm Y') := by
      simp [Af]
      rw [ReshapeBFn.eq.BFnReshape.of.Dvd]
      apply BmmBFn.eq.BFnBmm (f := f) h_mul h_sum
    have hsel : (Af.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ =
        F ((X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩) := by
      rw [hbmm]
      apply SelectBFn.eq.BFnSelect
    have hL : (F A).einsum C ≃ (Af.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hEf.trans ?_
      simp only [Af, Y', batch, k, F]
      rfl
    have hR : A.einsum C ≃ (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X', Y', batch, k]
      rfl
    exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => F t)).symm
  else if hgt : n > s'[s'.length - 2] then
    have hE := Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2 hs' hgt A C
    have hEf := Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2 hs' hgt (F A) C
    apply Bool.Eq.of.SEq
    let batch := s'.take (s'.length - 2)
    let n₀ := s'[s'.length - 2]
    let k' := s'[s'.length - 1]
    let Y0 : Tensor α (batch ++ [n₀, k']) :=
      cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm) C
    let Y' : Tensor α (batch ++ [n, k']) :=
      cast (by simp) (Y0.resize ⟨batch.length, by grind⟩ n)
    let X' := A.reshape (batch ++ [1, n]) (by simp)
    let Af := (F A).reshape (batch ++ [1, n]) (by simp)
    have hbmm : Af.bmm Y' = F (X'.bmm Y') := by
      simp [Af]
      rw [ReshapeBFn.eq.BFnReshape.of.Dvd]
      apply BmmBFn.eq.BFnBmm (f := f) h_mul h_sum
    have hsel : (Af.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ =
        F ((X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩) := by
      rw [hbmm]
      apply SelectBFn.eq.BFnSelect
    have hL : (F A).einsum C ≃ (Af.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hEf.trans ?_
      simp only [Af, Y', Y0, batch, n₀, k', F]
      rfl
    have hR : A.einsum C ≃ (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X', Y', Y0, batch, n₀, k']
      rfl
    exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => F t)).symm
  else
    have hlt := Nat.lt_of_le_of_ne (le_of_not_gt hgt) h_eq
    have hE := Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2 hs' hlt A C
    have hEf := Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2 hs' hlt (F A) C
    apply Bool.Eq.of.SEq
    let batch := s'.take (s'.length - 2)
    let n₀ := s'[s'.length - 2]
    let k' := s'[s'.length - 1]
    let Y' : Tensor α (batch ++ [n₀, k']) :=
      cast (congrArg (Tensor α) (by
        simp only [batch, n₀, k']
        exact (List.EqAppendTake__ListGet.of.GeLength_2 hs').symm)) C
    let A_r : Tensor α [n₀] := cast (by simp) (A.resize ⟨0, by grind⟩ n₀)
    let Af_r : Tensor α [n₀] := cast (by simp) ((F A).resize ⟨0, by grind⟩ n₀)
    have hr : Af_r = F A_r := by
      simp only [Af_r, A_r]
      rw [ResizeBFn.eq.BFnResize h0 A B ⟨0, by grind⟩ n₀]
      exact Cast_MapBFn.eq.MapCast.of.Eq (f := f) (by simp) _ B
    let X' := A_r.reshape (batch ++ [1, n₀]) (by simp)
    let Af := Af_r.reshape (batch ++ [1, n₀]) (by simp)
    have hx : Af = F X' := by
      simp only [Af, X', hr]
      apply ReshapeBFn.eq.BFnReshape.of.Dvd
    have hbmm : Af.bmm Y' = F (X'.bmm Y') := by
      rw [hx]
      apply BmmBFn.eq.BFnBmm (f := f) h_mul h_sum
    have hsel : (Af.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ =
        F ((X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩) := by
      rw [hbmm]
      apply SelectBFn.eq.BFnSelect
    have hL : (F A).einsum C ≃ (Af.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hEf.trans ?_
      simp only [Af, Y', Af_r, batch, n₀, k', F]
      rfl
    have hR : A.einsum C ≃ (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X', Y', A_r, batch, n₀, k']
      rfl
    exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans
      (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => F t)).symm


/-- `dot` commutes with a pointwise scalar binary operator `f` when the left rank is ≥ 2 and the right is a vector. -/
@[main]
private lemma left
  [Mul α] [Add α] [Zero α]
  {f : α → α → α}
-- given
  (h_mul : ∀ {s : List ℕ} (X C : Tensor α s) (B : Tensor α []), X.map (f · B.data[0]) * C = (X * C).map (f · B.data[0]))
  (h_sum : ∀ {s : List ℕ} (X : Tensor α s) (B : Tensor α []) (dim : ℕ), (X.map (f · B.data[0])).sum dim = (X.sum dim).map (f · B.data[0]))
  (h0 : ∀ b : α, f 0 b = 0)
  (hs : s.length ≥ 2)
  (A : Tensor α s)
  (C : Tensor α [n'])
  (B : Tensor α []) :
-- imply
  (A.map (f · B.data[0])) @ C = (A @ C).map (f · B.data[0]) := by
-- proof
  let F {s} (X : Tensor α s) : Tensor α s := X.map (f · B.data[0])
  simp only [Dot.dot]
  have hE := Einsum.as.SelectBmm.of.GeLength_2 hs A C
  have hEf := Einsum.as.SelectBmm.of.GeLength_2 hs (F A) C
  apply Bool.Eq.of.SEq
  let batch := s.take (s.length - 2)
  let k := s[s.length - 2]
  let n := s[s.length - 1]
  let K := n ⊔ n'
  let X0 : Tensor α (batch ++ [k, n]) :=
    cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
  let Af0 : Tensor α (batch ++ [k, n]) :=
    cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm) (F A)
  have hx0 : Af0 = F X0 :=
    Cast_MapBFn.eq.MapCast.of.Eq (f := f)
      (List.EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
  let X : Tensor α (batch ++ [k, K]) :=
    cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ K)
  let Af : Tensor α (batch ++ [k, K]) :=
    cast (by simp) (Af0.resize ⟨batch.length + 1, by grind⟩ K)
  have hX : Af = F X := by
    simp only [X, Af, hx0]
    rw [ResizeBFn.eq.BFnResize h0 X0 B ⟨batch.length + 1, by grind⟩ K]
    exact Cast_MapBFn.eq.MapCast.of.Eq (f := f) (by simp) _ B
  let Cr : Tensor α [K] := C.resize ⟨0, by grind⟩ K
  let Y' := Cr.reshape (batch ++ [K, 1]) (by simp)
  have hbmm : Af.bmm Y' = F (X.bmm Y') := by
    rw [hX]
    apply BmmBFn.eq.BFnBmm (f := f) h_mul h_sum
  have hsel : (Af.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ =
      F ((X.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩) := by
    rw [hbmm]
    apply SelectBFn.eq.BFnSelect
  have hL : (F A).einsum C ≃ (Af.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
    refine hEf.trans ?_
    simp only [Af, Af0, Y', Cr, batch, k, n, K, F]
    rfl
  have hR : A.einsum C ≃ (X.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
    refine hE.trans ?_
    simp only [X, X0, Y', Cr, batch, k, n, K]
    rfl
  exact hL.trans (Bool.SEq.of.Eq hsel) |>.trans
    (Bool.SEqUFnS.of.SEq hR (fun (t : Tensor α _) => F t)).symm


-- created on 2026-08-15
