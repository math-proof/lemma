import Lemma.Bool.SEq.is.Eq
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.Tensor.Dot.eq.TensorDotDataS
import Lemma.Tensor.Einsum.as.SelectBmm.of.Eq_Get_SubLength.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2
import Lemma.Tensor.Einsum.as.Tensordot.of.GeLength_2.GeLength_2
import Lemma.Tensor.Einsum.eq.SumMulDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.MapBmm.eq.BmmMapS.of.All_Eq_Add.All_Eq_Mul
import Lemma.Tensor.MapDot.eq.DotMapS.of.All_Eq_Mul
import Lemma.Tensor.MapCast.as.Map.of.Eq
import Lemma.Tensor.MapMul.eq.MulMap.of.All_Eq_Mul
import Lemma.Tensor.MapMul.eq.MulMapS.of.All_Eq_Mul
import Lemma.Tensor.MapTensordot.eq.TensordotMapS.of.All_Eq_Add.All_Eq_Mul
import Lemma.Tensor.ReshapeMap.eq.MapReshape.of.Dvd
import Lemma.Tensor.ResizeMap.eq.MapResize
import Lemma.Tensor.SelectMap.eq.MapSelect
import Lemma.Tensor.SEqMapS.of.SEq
import Lemma.Tensor.SumMap.eq.MapSum.of.All_EqUFnAdd
import Lemma.Vector.Dot.eq.SumMul
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.MapMul.eq.MulMapS.of.All_Eq_Mul
import Lemma.Vector.MapSum.eq.SumMap.of.All_EqUFnAdd
open Bool List Tensor Vector
set_option maxHeartbeats 2000000


/-- `dot` of 1-d tensors commutes with a pointwise map `f`. -/
@[main, comm]
private lemma une
  [Mul α] [AddCommMonoid α]
  [Mul β] [AddCancelCommMonoid β]
  {f : α → β}
-- given
  (h_mul : ∀ a b, f (a * b) = f a * f b)
  (h_add : ∀ a b, f (a + b) = f a + f b)
  (A : Tensor α [n])
  (B : Tensor α [n']) :
-- imply
  (A @ B).map f = (A.map f) @ (B.map f) := by
-- proof
  have h0 : f 0 = 0 := by
    have h := h_add 0 0
    simpa using h
  let K := n ⊔ n'
  let A' : Tensor α [K] := A.resize ⟨0, by grind⟩ K
  let B' : Tensor α [K] := B.resize ⟨0, by grind⟩ K
  let Af' : Tensor β [K] := (A.map f).resize ⟨0, by grind⟩ K
  let Bf' : Tensor β [K] := (B.map f).resize ⟨0, by grind⟩ K
  have hA : A @ B = A' @ B' := by
    simp only [Dot.dot]
    rw [Einsum.eq.SumMulDataS]
    simpa [A', B', K] using Einsum.eq.SumMulDataS.resize A B
  have hAf : (A.map f) @ (B.map f) = Af' @ Bf' := by
    simp only [Dot.dot]
    rw [Einsum.eq.SumMulDataS]
    simpa [Af', Bf', K] using Einsum.eq.SumMulDataS.resize (A.map f) (B.map f)
  have hAmap : A'.map f = Af' := by
    simp only [A', Af']
    exact (Tensor.ResizeMap.eq.MapResize h0 A ⟨0, by grind⟩ K).symm
  have hBmap : B'.map f = Bf' := by
    simp only [B', Bf']
    exact (Tensor.ResizeMap.eq.MapResize h0 B ⟨0, by grind⟩ K).symm
  rw [hA, hAf, ← hAmap, ← hBmap]
  have h_data : f (A'.data @ B'.data) = (A'.data.map f) @ (B'.data.map f) := by
    rw [Vector.Dot.eq.SumMul, Vector.Dot.eq.SumMul]
    rw [Vector.MapSum.eq.SumMap.of.All_EqUFnAdd h_add]
    rw [Vector.MapMul.eq.MulMapS.of.All_Eq_Mul h_mul]
  rw [Dot.eq.TensorDotDataS A' B']
  rw [Dot.eq.TensorDotDataS (A'.map f) (B'.map f)]
  apply Tensor.Eq.of.EqDataS
  apply Vector.Eq.of.All_EqGetS.fin
  intro i
  fin_cases i
  simp [Tensor.map, List.Vector.get]
  exact h_data


/-- `dot` commutes with a pointwise map `f`. -/
@[main, comm]
private lemma main
  [Mul α] [AddCommMonoid α]
  [Mul β] [AddCancelCommMonoid β]
  {f : α → β}
-- given
  (h_mul : ∀ a b, f (a * b) = f a * f b)
  (h_add : ∀ a b, f (a + b) = f a + f b)
  (A : Tensor α s)
  (B : Tensor α s') :
-- imply
  (A @ B).map f = (A.map f) @ (B.map f) := by
-- proof
  match s, s' with
  | [], _ =>
    apply MapDot.eq.DotMapS.of.All_Eq_Mul.left h_mul
  | _ :: _, [] =>
    apply MapDot.eq.DotMapS.of.All_Eq_Mul h_mul
  | [n], [n'] =>
    apply une h_mul h_add
  | n :: rest, s' =>
    if hboth : (n :: rest).length ≥ 2 ∧ s'.length ≥ 2 then
      have h0 : f 0 = 0 := by
        have h := h_add 0 0
        simpa using h
      let F {s} (X : Tensor α s) : Tensor β s := X.map f
      simp only [Dot.dot]
      have hE := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hboth.1 hboth.2 A B
      have hEf := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hboth.1 hboth.2 (F A) (F B)
      apply Bool.Eq.of.SEq
      let batch := (n :: rest).take ((n :: rest).length - 2)
      let batch' := s'.take (s'.length - 2)
      let m := (n :: rest)[(n :: rest).length - 2]
      let n₁ := (n :: rest)[(n :: rest).length - 1]
      let n' := s'[s'.length - 2]
      let k := s'[s'.length - 1]
      let K := n₁ ⊔ n'
      let X0 : Tensor α (batch ++ [m, n₁]) :=
        cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hboth.1).symm) A
      let Af0 : Tensor β (batch ++ [m, n₁]) :=
        cast (congrArg (Tensor β) (List.EqAppendTake__ListGet.of.GeLength_2 hboth.1).symm) (F A)
      have hAf0 : Af0 = F X0 :=
        Cast_Map.eq.MapCast.of.Eq (List.EqAppendTake__ListGet.of.GeLength_2 hboth.1).symm A f
      let X : Tensor α (batch ++ [m, K]) :=
        cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ K)
      let Af : Tensor β (batch ++ [m, K]) :=
        cast (by simp) (Af0.resize ⟨batch.length + 1, by grind⟩ K)
      have hAf : Af = F X := by
        simp only [Af, X, hAf0, F]
        rw [Tensor.ResizeMap.eq.MapResize h0]
        exact Cast_Map.eq.MapCast.of.Eq (by simp) _ f
      let Y0 : Tensor α (batch' ++ [n', k]) :=
        cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hboth.2).symm) B
      let Bf0 : Tensor β (batch' ++ [n', k]) :=
        cast (congrArg (Tensor β) (List.EqAppendTake__ListGet.of.GeLength_2 hboth.2).symm) (F B)
      have hBf0 : Bf0 = F Y0 :=
        Cast_Map.eq.MapCast.of.Eq (List.EqAppendTake__ListGet.of.GeLength_2 hboth.2).symm B f
      let Y : Tensor α (batch' ++ [K, k]) :=
        cast (by simp) (Y0.resize ⟨batch'.length, by grind⟩ K)
      let Bf : Tensor β (batch' ++ [K, k]) :=
        cast (by simp) (Bf0.resize ⟨batch'.length, by grind⟩ K)
      have hBf : Bf = F Y := by
        simp only [Bf, Y, hBf0, F]
        rw [Tensor.ResizeMap.eq.MapResize h0]
        exact Cast_Map.eq.MapCast.of.Eq (by simp) _ f
      have htd : F (X.tensordot Y) = Af.tensordot Bf := by
        rw [hAf, hBf]
        simp only [F]
        exact MapTensordot.eq.TensordotMapS.of.All_Eq_Add.All_Eq_Mul h_mul h_add X Y
      have hL : (F A).einsum (F B) ≃ Af.tensordot Bf := by
        refine hEf.trans ?_
        simp only [Af, Af0, Bf, Bf0, batch, batch', m, n₁, n', k, K, F]
        rfl
      have hR : A.einsum B ≃ X.tensordot Y := by
        refine hE.trans ?_
        simp only [X, X0, Y, Y0, batch, batch', m, n₁, n', k, K]
        rfl
      exact (SEqMapS.of.SEq hR f).trans (Bool.SEq.of.Eq htd) |>.trans hL.symm
    else if hvec : (n :: rest).length = 1 ∧ s'.length ≥ 2 then
      have hn : rest = [] := by aesop
      subst hn
      have h0 : f 0 = 0 := by
        have h := h_add 0 0
        simpa using h
      let F {s} (X : Tensor α s) : Tensor β s := X.map f
      simp only [Dot.dot]
      if heq : n = s'[s'.length - 2] then
        have hE := Einsum.as.SelectBmm.of.Eq_Get_SubLength.GeLength_2 hvec.2 heq A B
        have hEf := Einsum.as.SelectBmm.of.Eq_Get_SubLength.GeLength_2 hvec.2 heq (F A) (F B)
        apply Bool.Eq.of.SEq
        let batch := s'.take (s'.length - 2)
        let k := s'[s'.length - 1]
        let Y' : Tensor α (batch ++ [n, k]) :=
          cast (congrArg (Tensor α) (by
            simp only [batch, k]
            rw [heq]
            exact (List.EqAppendTake__ListGet.of.GeLength_2 hvec.2).symm)) B
        let Yf : Tensor β (batch ++ [n, k]) :=
          cast (congrArg (Tensor β) (by
            simp only [batch, k]
            rw [heq]
            exact (List.EqAppendTake__ListGet.of.GeLength_2 hvec.2).symm)) (F B)
        have hY : Yf = F Y' :=
          Cast_Map.eq.MapCast.of.Eq (by
            simp only [batch, k]
            rw [heq]
            exact (List.EqAppendTake__ListGet.of.GeLength_2 hvec.2).symm) B f
        let X' := A.reshape (batch ++ [1, n]) (by simp)
        let Af := (F A).reshape (batch ++ [1, n]) (by simp)
        have hX : Af = F X' := by
          simp only [Af, X', F]
          exact ReshapeMap.eq.MapReshape.of.Dvd (by simp) A
        have hbmm : (F X').bmm (F Y') = F (X'.bmm Y') := by
          simp only [F]
          exact (MapBmm.eq.BmmMapS.of.All_Eq_Add.All_Eq_Mul h_mul h_add X' Y').symm
        have hsel :
            ((F X').bmm (F Y')).select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ =
              F ((X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩) := by
          rw [hbmm]
          simp only [F]
          exact SelectMap.eq.MapSelect (X'.bmm Y') ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩
        have hL : (F A).einsum (F B) ≃ (Af.bmm Yf).select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
          refine hEf.trans ?_
          simp only [Af, Yf, batch, k, F]
          rfl
        have hR : A.einsum B ≃ (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
          refine hE.trans ?_
          simp only [X', Y', batch, k]
          rfl
        have hmid : Af.bmm Yf = F (X'.bmm Y') := by
          rw [hX, hY]
          exact hbmm
        have hF : F ((X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩) =
            (Af.bmm Yf).select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
          rw [← hsel, hbmm, hmid]
        exact (SEqMapS.of.SEq hR f).trans (Bool.SEq.of.Eq hF) |>.trans hL.symm
      else if hgt : n > s'[s'.length - 2] then
        have hE := Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2 hvec.2 hgt A B
        have hEf := Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2 hvec.2 hgt (F A) (F B)
        apply Bool.Eq.of.SEq
        let batch := s'.take (s'.length - 2)
        let n₀ := s'[s'.length - 2]
        let k' := s'[s'.length - 1]
        let Y0 : Tensor α (batch ++ [n₀, k']) :=
          cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hvec.2).symm) B
        let Yf0 : Tensor β (batch ++ [n₀, k']) :=
          cast (congrArg (Tensor β) (List.EqAppendTake__ListGet.of.GeLength_2 hvec.2).symm) (F B)
        have hY0 : Yf0 = F Y0 :=
          Cast_Map.eq.MapCast.of.Eq (List.EqAppendTake__ListGet.of.GeLength_2 hvec.2).symm B f
        let Y' : Tensor α (batch ++ [n, k']) :=
          cast (by simp) (Y0.resize ⟨batch.length, by grind⟩ n)
        let Yf : Tensor β (batch ++ [n, k']) :=
          cast (by simp) (Yf0.resize ⟨batch.length, by grind⟩ n)
        have hY : Yf = F Y' := by
          simp only [Yf, Y', hY0, F]
          rw [Tensor.ResizeMap.eq.MapResize h0]
          exact Cast_Map.eq.MapCast.of.Eq (by simp) _ f
        let X' := A.reshape (batch ++ [1, n]) (by simp)
        let Af := (F A).reshape (batch ++ [1, n]) (by simp)
        have hX : Af = F X' := by
          simp only [Af, X', F]
          exact ReshapeMap.eq.MapReshape.of.Dvd (by simp) A
        have hbmm : (F X').bmm (F Y') = F (X'.bmm Y') := by
          simp only [F]
          exact (MapBmm.eq.BmmMapS.of.All_Eq_Add.All_Eq_Mul h_mul h_add X' Y').symm
        have hsel :
            ((F X').bmm (F Y')).select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ =
              F ((X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩) := by
          rw [hbmm]
          simp only [F]
          exact SelectMap.eq.MapSelect (X'.bmm Y') ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩
        have hL : (F A).einsum (F B) ≃ (Af.bmm Yf).select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
          refine hEf.trans ?_
          simp only [Af, Yf, Yf0, batch, n₀, k', F]
          rfl
        have hR : A.einsum B ≃ (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
          refine hE.trans ?_
          simp only [X', Y', Y0, batch, n₀, k']
          rfl
        have hmid : Af.bmm Yf = F (X'.bmm Y') := by
          rw [hX, hY]
          exact hbmm
        have hF : F ((X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩) =
            (Af.bmm Yf).select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
          rw [← hsel, hbmm, hmid]
        exact (SEqMapS.of.SEq hR f).trans (Bool.SEq.of.Eq hF) |>.trans hL.symm
      else
        have hne : n ≠ s'[s'.length - 2] := heq
        have hlt : n < s'[s'.length - 2] := Nat.lt_of_le_of_ne (le_of_not_gt hgt) hne
        have hE := Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2 hvec.2 hlt A B
        have hEf := Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2 hvec.2 hlt (F A) (F B)
        apply Bool.Eq.of.SEq
        let batch := s'.take (s'.length - 2)
        let n₀ := s'[s'.length - 2]
        let k' := s'[s'.length - 1]
        let Y0 : Tensor α (batch ++ [n₀, k']) :=
          cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hvec.2).symm) B
        let Yf0 : Tensor β (batch ++ [n₀, k']) :=
          cast (congrArg (Tensor β) (List.EqAppendTake__ListGet.of.GeLength_2 hvec.2).symm) (F B)
        have hY0 : Yf0 = F Y0 :=
          Cast_Map.eq.MapCast.of.Eq (List.EqAppendTake__ListGet.of.GeLength_2 hvec.2).symm B f
        let A_r : Tensor α [n₀] := A.resize ⟨0, by grind⟩ n₀
        let Af_r : Tensor β [n₀] := (F A).resize ⟨0, by grind⟩ n₀
        have hr : Af_r = F A_r := by
          simp only [Af_r, A_r, F]
          exact Tensor.ResizeMap.eq.MapResize h0 A ⟨0, by grind⟩ n₀
        let X' := A_r.reshape (batch ++ [1, n₀]) (by simp)
        let Af := Af_r.reshape (batch ++ [1, n₀]) (by simp)
        have hX : Af = F X' := by
          simp only [Af, X', hr, F]
          exact ReshapeMap.eq.MapReshape.of.Dvd (by simp) A_r
        have hbmm : (F X').bmm (F Y0) = F (X'.bmm Y0) := by
          simp only [F]
          exact (MapBmm.eq.BmmMapS.of.All_Eq_Add.All_Eq_Mul h_mul h_add X' Y0).symm
        have hsel :
            ((F X').bmm (F Y0)).select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ =
              F ((X'.bmm Y0).select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩) := by
          rw [hbmm]
          simp only [F]
          exact SelectMap.eq.MapSelect (X'.bmm Y0) ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩
        have hL : (F A).einsum (F B) ≃ (Af.bmm Yf0).select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
          refine hEf.trans ?_
          simp only [Af, Af_r, Yf0, batch, n₀, k', F]
          rfl
        have hR : A.einsum B ≃ (X'.bmm Y0).select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
          refine hE.trans ?_
          simp only [X', A_r, Y0, batch, n₀, k']
          rfl
        have hmid : Af.bmm Yf0 = F (X'.bmm Y0) := by
          rw [hX, hY0]
          exact hbmm
        have hF : F ((X'.bmm Y0).select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩) =
            (Af.bmm Yf0).select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
          rw [← hsel, hbmm, hmid]
        exact (SEqMapS.of.SEq hR f).trans (Bool.SEq.of.Eq hF) |>.trans hL.symm
    else if hleft : (n :: rest).length ≥ 2 ∧ s'.length = 1 then
      match s' with
      | [] =>
        grind
      | d :: t =>
        have ht : t = [] := by aesop
        subst ht
        have h0 : f 0 = 0 := by
          have h := h_add 0 0
          simpa using h
        let F {s} (X : Tensor α s) : Tensor β s := X.map f
        simp only [Dot.dot]
        have hE := Einsum.as.SelectBmm.of.GeLength_2 hleft.1 A B
        have hEf := Einsum.as.SelectBmm.of.GeLength_2 hleft.1 (F A) (F B)
        apply Bool.Eq.of.SEq
        let batch := (n :: rest).take ((n :: rest).length - 2)
        let k := (n :: rest)[(n :: rest).length - 2]
        let n₀ := (n :: rest)[(n :: rest).length - 1]
        let K := n₀ ⊔ d
        let X0 : Tensor α (batch ++ [k, n₀]) :=
          cast (congrArg (Tensor α) (List.EqAppendTake__ListGet.of.GeLength_2 hleft.1).symm) A
        let Af0 : Tensor β (batch ++ [k, n₀]) :=
          cast (congrArg (Tensor β) (List.EqAppendTake__ListGet.of.GeLength_2 hleft.1).symm) (F A)
        have hx0 : Af0 = F X0 :=
          Cast_Map.eq.MapCast.of.Eq (List.EqAppendTake__ListGet.of.GeLength_2 hleft.1).symm A f
        let X : Tensor α (batch ++ [k, K]) :=
          cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ K)
        let Af : Tensor β (batch ++ [k, K]) :=
          cast (by simp) (Af0.resize ⟨batch.length + 1, by grind⟩ K)
        have hX : Af = F X := by
          simp only [X, Af, hx0, F]
          rw [Tensor.ResizeMap.eq.MapResize h0]
          exact Cast_Map.eq.MapCast.of.Eq (by simp) _ f
        let Cr : Tensor α [K] := B.resize ⟨0, by grind⟩ K
        let Crf : Tensor β [K] := (F B).resize ⟨0, by grind⟩ K
        have hC : Crf = F Cr := by
          simp only [Cr, Crf, F]
          exact Tensor.ResizeMap.eq.MapResize h0 B ⟨0, by grind⟩ K
        let Y' := Cr.reshape (batch ++ [K, 1]) (by simp)
        let Yf := Crf.reshape (batch ++ [K, 1]) (by simp)
        have hY : Yf = F Y' := by
          simp only [Yf, Y', hC, F]
          exact ReshapeMap.eq.MapReshape.of.Dvd (by simp) Cr
        have hbmm : (F X).bmm (F Y') = F (X.bmm Y') := by
          simp only [F]
          exact (MapBmm.eq.BmmMapS.of.All_Eq_Add.All_Eq_Mul h_mul h_add X Y').symm
        have hsel :
            ((F X).bmm (F Y')).select ⟨(n :: rest).length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ =
              F ((X.bmm Y').select ⟨(n :: rest).length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩) := by
          rw [hbmm]
          simp only [F]
          exact SelectMap.eq.MapSelect (X.bmm Y') ⟨(n :: rest).length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩
        have hL : (F A).einsum (F B) ≃ (Af.bmm Yf).select ⟨(n :: rest).length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
          refine hEf.trans ?_
          simp only [Af, Af0, Yf, Crf, batch, k, n₀, K, F]
          rfl
        have hR : A.einsum B ≃ (X.bmm Y').select ⟨(n :: rest).length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
          refine hE.trans ?_
          simp only [X, X0, Y', Cr, batch, k, n₀, K]
          rfl
        have hmid : Af.bmm Yf = F (X.bmm Y') := by
          rw [hX, hY]
          exact hbmm
        have hF : F ((X.bmm Y').select ⟨(n :: rest).length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩) =
            (Af.bmm Yf).select ⟨(n :: rest).length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
          rw [← hsel, hbmm, hmid]
        exact (SEqMapS.of.SEq hR f).trans (Bool.SEq.of.Eq hF) |>.trans hL.symm
    else
      cases s' with
      | nil =>
        apply MapDot.eq.DotMapS.of.All_Eq_Mul h_mul
      | cons _ t =>
        have ht : t = [] := by aesop
        subst ht
        have hn : rest = [] := by aesop
        subst hn
        apply une h_mul h_add


-- created on 2026-08-16
-- updated on 2026-08-17
