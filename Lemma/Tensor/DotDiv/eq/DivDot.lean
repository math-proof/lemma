import Lemma.Tensor.Div.eq.Div_GetData_0
import Lemma.Tensor.Dot.eq.SumMul
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.Dot.as.SumMul
import Lemma.Tensor.Dot.eq.GetSumMul
import Lemma.Tensor.Dot.eq.SumMul.of.Lt
import Lemma.Tensor.Dot.eq.SumMul.of.Ge
import Lemma.Tensor.Dot.eq.SelectDot_Unsqueeze_1
import Lemma.Tensor.Einsum.eq.MulGetData_0
import Lemma.Tensor.Einsum.eq.SumMulDataS.of.Gt
import Lemma.Tensor.Einsum.eq.SumMulDataS.of.Lt
import Lemma.Tensor.Einsum.as.SelectBmm.of.Eq_Get_SubLength.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.EqGet_SubLength_1.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.GeGet_SubLength_1.GeLength_2
import Lemma.Tensor.Einsum.as.SelectBmm.of.LtGet_SubLength_1.GeLength_2
import Lemma.Tensor.Einsum.as.Tensordot.of.GeLength_2.GeLength_2
import Lemma.Tensor.Matmul.as.MatmulResizeS.of.Length.GtLength_0
import Lemma.Tensor.GetMatmul.as.MatmulGetS.of.Get_0.Length.GtLength_0
import Lemma.Tensor.SelectDiv.eq.DivSelectS
import Lemma.Tensor.SEqTensordotS.of.SEq.SEq.Eq.Eq
import Lemma.Tensor.SelectTensorReplicateProd.eq.TensorReplicateProdEraseIdx
import Lemma.Tensor.SumDiv.eq.DivSum
import Lemma.Tensor.Tensordot.as.Matmul.of.GeLengthS
import Lemma.Tensor.Tensordot.as.Matmul.of.LtLengthS
import Lemma.Vector.FlattenMap.eq.MapFlatten
import Lemma.Vector.GetMap₂.eq.BFnGetS
import Lemma.Vector.SplitAtMap.eq.MapSplitAt
open Nat List Tensor Vector Bool

set_option maxHeartbeats 8000000


private lemma mul_div_tensor
  [Semifield α]
-- given
  (A C : Tensor α s)
  (B : Tensor α []) :
-- imply
  (A / B) * C = (A * C) / B := by
-- proof
  apply Eq.of.EqDataS
  apply Vector.Eq.of.All_EqGetS.fin
  intro i
  dsimp only [Mul.mul, HDiv.hDiv, HMul.hMul]
  erw [GetMap₂.eq.BFnGetS.fin]
  erw [GetMap.eq.UFnGet (i := i)]
  erw [GetMap.eq.UFnGet (i := i)]
  erw [GetMap₂.eq.BFnGetS.fin]
  exact div_mul_eq_mul_div (α := α) _ _ _


private lemma left_scalar_mul_div
  [Semifield α]
-- given
  (a B : α)
  (C : Tensor α s) :
-- imply
  (a / B) * C = (a * C) / B := by
-- proof
  apply Eq.of.EqDataS
  apply Vector.Eq.of.All_EqGetS.fin
  intro i
  dsimp only [HMul.hMul, HDiv.hDiv]
  erw [GetMap.eq.UFnGet (i := i)]
  erw [GetMap.eq.UFnGet (i := i)]
  erw [GetMap.eq.UFnGet (i := i)]
  exact div_mul_eq_mul_div (α := α) _ _ _


private lemma right_mul_div
  [Semifield α]
-- given
  (A : Tensor α s)
  (b B : α) :
-- imply
  (A / B) * b = (A * b) / B := by
-- proof
  apply Eq.of.EqDataS
  apply Vector.Eq.of.All_EqGetS.fin
  intro i
  dsimp only [HMul.hMul, HDiv.hDiv]
  erw [GetMap.eq.UFnGet (i := i)]
  erw [GetMap.eq.UFnGet (i := i)]
  erw [GetMap.eq.UFnGet (i := i)]
  erw [GetMap.eq.UFnGet (i := i)]
  exact div_mul_eq_mul_div (α := α) _ _ _


private lemma vector_map_div_repeat
  [DivisionSemiring α]
-- given
  (v : List.Vector α n)
  (b : α)
  (d : ℕ) :
-- imply
  (v.map (· / b)).repeat d = (v.repeat d).map (· / b) := by
-- proof
  apply Vector.Eq.of.All_EqGetS.fin
  intro i
  erw [GetMap.eq.UFnGet (i := i)]
  erw [GetRepeat.eq.Get_Mod.of.Lt_Mul.fin]
  erw [GetRepeat.eq.Get_Mod.of.Lt_Mul.fin]
  erw [GetMap.eq.UFnGet]


private lemma vector_resize_div
  [Semifield α]
-- given
  (v : List.Vector α n)
  (c : α)
  (m : ℕ) :
-- imply
  (v.map (· / c)).resize m = (v.resize m).map (· / c) := by
-- proof
  apply Vector.Eq.of.All_EqGetS.fin
  intro i
  have hL : ((v.map (· / c)).resize m)[i] =
      if h : ↑i < m / n * n then (v.map (· / c))[↑i % n]'(LtMod.of.Lt_Mul h) else 0 :=
    GetResize.eq.Ite_Get_Mod.fin (v.map (· / c)) m i
  have hR : (v.resize m)[i] =
      if h : ↑i < m / n * n then v[↑i % n]'(LtMod.of.Lt_Mul h) else 0 :=
    GetResize.eq.Ite_Get_Mod.fin v m i
  change ((v.map (· / c)).resize m)[i] = ((v.resize m).map (· / c))[i]
  rw [hL]
  have hmap : ((v.resize m).map (· / c))[i] = (v.resize m)[i] / c := by
    change List.Vector.get _ i = _
    rw [List.Vector.get_map]
    rfl
  rw [hmap, hR]
  split_ifs with h
  ·
    change List.Vector.get (v.map (· / c)) _ = List.Vector.get v _ / c
    rw [List.Vector.get_map]
  ·
    exact (zero_div c).symm


private lemma cast_map
-- given
  (h : n = n')
  (v : List.Vector α n)
  (f : α → α) :
-- imply
  cast (congrArg (List.Vector α) h) (v.map f) =
    (cast (congrArg (List.Vector α) h) v).map f := by
-- proof
  subst h
  rfl


private lemma reshape_div
  [Semifield α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (s' : List ℕ)
  (h : s.prod ∣ s'.prod) :
-- imply
  (X / B).reshape s' h = X.reshape s' h / B := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.reshape
  dsimp only [HDiv.hDiv]
  have h_rep := vector_map_div_repeat X.data B.data[0] (s'.prod / s.prod)
  have h_len := EqMulDiv.of.Dvd h
  rw [← cast_map h_len]
  exact congrArg (cast (congrArg (List.Vector α) h_len)) h_rep


private lemma unsqueeze_div
  [Semifield α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : ℕ) :
-- imply
  (X / B).unsqueeze dim = X.unsqueeze dim / B := by
-- proof
  simp only [Tensor.unsqueeze]
  exact reshape_div X B _ _


private lemma repeat_div
  [Semifield α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : Fin s.length)
  (n : ℕ) :
-- imply
  (X / B).repeat dim n = X.repeat dim n / B := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.repeat
  dsimp only [HDiv.hDiv]
  let b := B.data[0]
  have h_flat :
      (((X.data.map (fun x => x / b)).splitAt ↑dim).map (List.Vector.repeat · n)).flatten =
        ((((X.data.splitAt ↑dim).map (List.Vector.repeat · n)).flatten).map (fun y => y / b)) := by
    rw [SplitAtMap.eq.MapSplitAt]
    rw [MapMap.eq.Map_Comp]
    have h_inner :
        ((X.data.splitAt ↑dim).map fun v =>
            List.Vector.repeat (v.map fun x => x / b) n) =
          ((X.data.splitAt ↑dim).map fun v =>
            (List.Vector.repeat v n).map fun x => x / b) := by
      congr 1
      funext v
      exact vector_map_div_repeat v b n
    change ((X.data.splitAt ↑dim).map fun v =>
        List.Vector.repeat (v.map fun x => x / b) n).flatten =
      ((((X.data.splitAt ↑dim).map (List.Vector.repeat · n)).flatten).map fun y => y / b)
    rw [h_inner]
    conv_lhs =>
      arg 1
      rw [show (fun v => (v.repeat n).map fun x => x / b) =
              ((fun w => w.map fun x => x / b) ∘ (List.Vector.repeat · n)) from rfl]
      rw [Map_Comp.eq.MapMap]
    rw [FlattenMap.eq.MapFlatten]
  have h_prod := (ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength dim.isLt n).symm
  rw [← cast_map h_prod]
  exact congrArg (cast (congrArg (List.Vector α) h_prod)) h_flat


private lemma resize_div
  [Semifield α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : Fin s.length)
  (n : ℕ) :
-- imply
  (X / B).resize dim n = X.resize dim n / B := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.resize
  dsimp only [HDiv.hDiv]
  let b := B.data[0]
  let r := n * (s.drop dim.succ).prod
  have h_flat :
      (((X.data.map (fun x => x / b)).splitAt ↑dim).map (List.Vector.resize · r)).flatten =
        ((((X.data.splitAt ↑dim).map (List.Vector.resize · r)).flatten).map (fun y => y / b)) := by
    rw [SplitAtMap.eq.MapSplitAt]
    rw [MapMap.eq.Map_Comp]
    have h_inner :
        ((X.data.splitAt ↑dim).map fun v => List.Vector.resize (v.map fun x => x / b) r) =
          ((X.data.splitAt ↑dim).map fun v => (List.Vector.resize v r).map fun x => x / b) := by
      congr 1
      funext v
      exact vector_resize_div v b r
    change ((X.data.splitAt ↑dim).map fun v => List.Vector.resize (v.map fun x => x / b) r).flatten =
      ((((X.data.splitAt ↑dim).map (List.Vector.resize · r)).flatten).map fun y => y / b)
    rw [h_inner]
    conv_lhs =>
      arg 1
      rw [show (fun v => (v.resize r).map fun x => x / b) =
              ((fun w => w.map fun x => x / b) ∘ (List.Vector.resize · r)) from rfl]
      rw [Map_Comp.eq.MapMap]
    rw [FlattenMap.eq.MapFlatten]
  have h_prod := MulProd_Mul_Prod.eq.ProdSet.of.GtLength dim.isLt n
  rw [show r = n * (s.drop dim.succ).prod from rfl] at h_flat
  rw [← cast_map h_prod]
  exact congrArg (cast (congrArg (List.Vector α) h_prod)) h_flat


private lemma cast_div
  [Div α]
  {s s' : List ℕ}
-- given
  (h : s = s')
  (X : Tensor α s)
  (B : Tensor α []) :
-- imply
  (cast (congrArg (Tensor α) h) (X / B) : Tensor α s') =
    cast (congrArg (Tensor α) h) X / B := by
-- proof
  subst h
  rfl


private lemma select_div
  [Div α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  (X / B).select d i = X.select d i / B := by
-- proof
  let R : Tensor α s := ⟨List.Vector.replicate s.prod B.data[0]⟩
  have hX : X / B = X / R := by
    apply Eq.of.EqDataS
    simp only [HDiv.hDiv, R]
    exact Div.eq.Div_Replicate X.data B.data[0]
  rw [hX]
  simp only [R]
  rw [SelectDiv.eq.DivSelectS]
  rw [SelectTensorReplicateProd.eq.TensorReplicateProdEraseIdx]
  apply Eq.of.EqDataS
  simp only [HDiv.hDiv]
  exact (Div.eq.Div_Replicate (X.select d i).data B.data[0]).symm


private lemma vector_vector
  [Semifield α]
-- given
  (A C : Tensor α [n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  repeat rw [Dot.eq.SumMul__0]
  rw [mul_div_tensor]
  exact SumDiv.eq.DivSum (A * C) B 0


private lemma vector_vector_lt
  [Semifield α]
-- given
  (h : n < n')
  (A : Tensor α [n])
  (C : Tensor α [n'])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  rw [Einsum.eq.SumMulDataS.of.Lt h (X := A / B) (Y := C)]
  rw [Einsum.eq.SumMulDataS.of.Lt h (X := A) (Y := C)]
  have h_cast :
      (cast (by simp) ((A / B).resize ⟨0, by simp⟩ n') : Tensor α [n']) =
        (cast (by simp) (A.resize ⟨0, by simp⟩ n') : Tensor α [n']) / B := by
    rw [resize_div]
    exact (CastDiv.eq.DivCast.of.Eq.scalar (by simp) (A.resize ⟨0, by simp⟩ n') B).symm
  erw [h_cast]
  rw [mul_div_tensor]
  exact SumDiv.eq.DivSum _ B 0


private lemma vector_vector_gt
  [Semifield α]
-- given
  (h : n > n')
  (A : Tensor α [n])
  (C : Tensor α [n'])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  rw [Einsum.eq.SumMulDataS.of.Gt h (X := A / B) (Y := C)]
  rw [Einsum.eq.SumMulDataS.of.Gt h (X := A) (Y := C)]
  have h_mul :
      (A / B) * (cast (by simp) (C.resize ⟨0, by simp⟩ n) : Tensor α [n]) =
        (A * (cast (by simp) (C.resize ⟨0, by simp⟩ n) : Tensor α [n])) / B :=
    mul_div_tensor A _ B
  erw [h_mul]
  exact SumDiv.eq.DivSum _ B 0


private lemma left_nil
  [Semifield α]
-- given
  (A : Tensor α [])
  (B : Tensor α [])
  (C : Tensor α s') :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  rw [Einsum.eq.MulGetData_0 (X := A / B), Einsum.eq.MulGetData_0 (X := A)]
  have h : (A / B).data[0] = A.data[0] / B.data[0] := by
    simp [HDiv.hDiv]
    rfl
  rw [h]
  refine (left_scalar_mul_div (A.data[0]) B.data[0] C).trans ?_
  rfl


private lemma right_nil
  [Semifield α]
-- given
  (A : Tensor α (n :: s))
  (B : Tensor α [])
  (C : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  simp only [Dot.dot]
  unfold einsum
  simp
  have h_shape : matmul_shape (n :: s) [] = n :: s := by
    simp [matmul_shape]
  have h_mul : (A / B) * C.data[0] = (A * C.data[0]) / B := by
    rw [Div.eq.Div_GetData_0 A B, Div.eq.Div_GetData_0 (A * C.data[0]) B]
    exact right_mul_div A C.data[0] B.data[0]
  refine Eq.trans (congrArg (cast (by simp [matmul_shape])) h_mul) ?_
  exact CastDiv.eq.DivCast.of.Eq.scalar h_shape.symm (A * C.data[0]) B


private lemma matrix_matrix
  [Semifield α]
-- given
  (A : Tensor α [m, k])
  (C : Tensor α [k, n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  let A_div0 : Tensor α [m, 1, k] := (A / B).unsqueeze 1
  let A_div : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨1, by grind⟩ n)
  let A0 : Tensor α [m, 1, k] := A.unsqueeze 1
  let A' : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ n)
  let CT : Tensor α [n, k] := Cᵀ
  let C0 : Tensor α [1, n, k] := CT.unsqueeze 0
  let C' : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ m)
  have hL : (A / B) @ C = (A_div * C').sum 2 := by
    simpa [A_div, A_div0, C', C0, CT] using Dot.eq.SumMul (A / B) C
  have hR : A @ C = (A' * C').sum 2 := by
    simpa [A', A0, C', C0, CT] using Dot.eq.SumMul A C
  rw [hL, hR]
  have hA : A_div = A' / B := by
    have h0 : A_div0 = A0 / B := by
      simp only [A_div0, A0]
      convert unsqueeze_div A B 1 <;> simp
    simp only [A_div, A']
    rw [h0]
    have hr := repeat_div A0 B ⟨1, by grind⟩ n
    rw [hr]
    exact cast_div (by simp) _ B
  rw [hA, mul_div_tensor]
  exact SumDiv.eq.DivSum _ B 2


private lemma matrix_matrix_lt
  [Semifield α]
-- given
  (h : k' < k)
  (A : Tensor α [m, k'])
  (C : Tensor α [k, n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  let A_div_r : Tensor α [m, k] := (A / B).resize ⟨1, by grind⟩ k
  let A_r : Tensor α [m, k] := A.resize ⟨1, by grind⟩ k
  have hr : A_div_r = A_r / B := by
    simp only [A_div_r, A_r]
    exact resize_div A B ⟨1, by grind⟩ k
  let A_div0 : Tensor α [m, 1, k] := A_div_r.unsqueeze 1
  let A0 : Tensor α [m, 1, k] := A_r.unsqueeze 1
  have h0 : A_div0 = A0 / B := by
    simp only [A_div0, A0, hr]
    convert unsqueeze_div A_r B 1 <;> simp
  let A_div : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨1, by grind⟩ n)
  let A' : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ n)
  let CT : Tensor α [n, k] := Cᵀ
  let C0 : Tensor α [1, n, k] := CT.unsqueeze 0
  let C' : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ m)
  have hA : A_div = A' / B := by
    simp only [A_div, A']
    rw [h0, repeat_div A0 B ⟨1, by grind⟩ n]
    exact cast_div (by simp) _ B
  have hL : (A / B) @ C = (A_div * C').sum 2 := by
    simpa [A_div, A_div0, A_div_r, C', C0, CT] using Dot.eq.SumMul.of.Lt h (A / B) C
  have hR : A @ C = (A' * C').sum 2 := by
    simpa [A', A0, A_r, C', C0, CT] using Dot.eq.SumMul.of.Lt h A C
  rw [hL, hR, hA, mul_div_tensor]
  exact SumDiv.eq.DivSum _ B 2


private lemma matrix_matrix_ge
  [Semifield α]
-- given
  (h : k ≥ k')
  (A : Tensor α [m, k])
  (C : Tensor α [k', n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  let A_div0 : Tensor α [m, 1, k] := (A / B).unsqueeze 1
  let A0 : Tensor α [m, 1, k] := A.unsqueeze 1
  have h0 : A_div0 = A0 / B := by
    simp only [A_div0, A0]
    convert unsqueeze_div A B 1 <;> simp
  let A_div : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨1, by grind⟩ n)
  let A' : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ n)
  let C_r : Tensor α [k, n] := C.resize ⟨0, by grind⟩ k
  let CT : Tensor α [n, k] := C_rᵀ
  let C0 : Tensor α [1, n, k] := CT.unsqueeze 0
  let C' : Tensor α [m, n, k] :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ m)
  have hA : A_div = A' / B := by
    simp only [A_div, A']
    rw [h0, repeat_div A0 B ⟨1, by grind⟩ n]
    exact cast_div (by simp) _ B
  have hL : (A / B) @ C = (A_div * C').sum 2 := by
    simpa [A_div, A_div0, C', C0, CT, C_r] using Dot.eq.SumMul.of.Ge h (A / B) C
  have hR : A @ C = (A' * C').sum 2 := by
    simpa [A', A0, C', C0, CT, C_r] using Dot.eq.SumMul.of.Ge h A C
  rw [hL, hR, hA, mul_div_tensor]
  exact SumDiv.eq.DivSum _ B 2

private lemma vector_matrix
  [Semifield α]
-- given
  (A : Tensor α [n])
  (C : Tensor α [k, d])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  let K := n ⊔ k
  let A_div_r : Tensor α [K] := (A / B).resize ⟨0, by grind⟩ K
  let A_r : Tensor α [K] := A.resize ⟨0, by grind⟩ K
  have hr : A_div_r = A_r / B := by
    simp only [A_div_r, A_r]
    exact resize_div A B ⟨0, by grind⟩ K
  let C_r : Tensor α [K, d] := C.resize ⟨0, by grind⟩ K
  let Adu0 : Tensor α [1, K] := A_div_r.unsqueeze 0
  let Au0 : Tensor α [1, K] := A_r.unsqueeze 0
  have hu0 : Adu0 = Au0 / B := by
    simp only [Adu0, Au0, hr]
    convert unsqueeze_div A_r B 0 <;> simp
  let A_div0 : Tensor α [1, 1, K] := Adu0.unsqueeze 1
  let A0 : Tensor α [1, 1, K] := Au0.unsqueeze 1
  have h0 : A_div0 = A0 / B := by
    simp only [A_div0, A0, hu0]
    convert unsqueeze_div Au0 B 1 <;> simp
  let A_div : Tensor α [1, d, K] :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨1, by grind⟩ d)
  let A' : Tensor α [1, d, K] :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨1, by grind⟩ d)
  let CT : Tensor α [d, K] := C_rᵀ
  let C0 : Tensor α [1, d, K] := CT.unsqueeze 0
  let C' : Tensor α [1, d, K] :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨0, by grind⟩ 1)
  have hA : A_div = A' / B := by
    simp only [A_div, A']
    rw [h0, repeat_div A0 B ⟨1, by grind⟩ d]
    exact cast_div (by simp) _ B
  have hL : (A / B) @ C = ((A_div * C').sum 2).get ⟨0, by grind⟩ := by
    simpa [A_div, A_div0, Adu0, A_div_r, C', C0, CT, C_r, K] using
      Dot.eq.GetSumMul.resize (A / B) C
  have hR : A @ C = ((A' * C').sum 2).get ⟨0, by grind⟩ := by
    simpa [A', A0, Au0, A_r, C', C0, CT, C_r, K] using
      Dot.eq.GetSumMul.resize A C
  rw [hL, hR]
  have h_sum : (A_div * C').sum 2 = (A' * C').sum 2 / B := by
    rw [hA, mul_div_tensor, SumDiv.eq.DivSum]
  rw [h_sum]
  exact GetDiv.eq.DivGet ((A' * C').sum 2) B ⟨0, by simp⟩


private lemma matrix_vector
  [Semifield α]
-- given
  (A : Tensor α [m, k])
  (C : Tensor α [d])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  rw [Dot.eq.SelectDot_Unsqueeze_1 (A / B) C]
  rw [Dot.eq.SelectDot_Unsqueeze_1 A C]
  have h : ((A / B) @ (C.unsqueeze 1)) = (A @ (C.unsqueeze 1)) / B := by
    if h : k = d then
      subst h
      exact matrix_matrix A (C.unsqueeze 1) B
    else if hlt : d < k then
      exact matrix_matrix_ge (le_of_lt hlt) A (C.unsqueeze 1) B
    else
      have hlt' : k < d := Nat.lt_of_le_of_ne (le_of_not_gt hlt) h
      exact matrix_matrix_lt hlt' A (C.unsqueeze 1) B
  have hsel :=
    congrArg
      (fun t : Tensor α (matmul_shape [m, k] [d, 1]) =>
        t.select ⟨1, by simp [matmul_shape]⟩ ⟨0, by simp [matmul_shape, broadcast_shape]⟩)
      h
  exact hsel.trans (select_div (A @ (C.unsqueeze 1)) B ⟨1, by simp [matmul_shape]⟩
    ⟨0, by simp [matmul_shape, broadcast_shape]⟩)


private lemma vector_vector_any
  [Semifield α]
-- given
  (A : Tensor α [n])
  (C : Tensor α [n'])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  if h : n = n' then
    subst h
    exact vector_vector A C B
  else if hlt : n < n' then
    exact vector_vector_lt hlt A C B
  else
    have hgt : n > n' := Nat.lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm h)
    exact vector_vector_gt hgt A C B


private lemma matrix_matrix_any
  [Semifield α]
-- given
  (A : Tensor α [m, k])
  (C : Tensor α [k', n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  if h : k = k' then
    subst h
    exact matrix_matrix A C B
  else if hlt : k' < k then
    exact matrix_matrix_ge (le_of_lt hlt) A C B
  else
    have hlt' : k < k' := Nat.lt_of_le_of_ne (le_of_not_gt hlt) h
    exact matrix_matrix_lt hlt' A C B


/-- Batched matmul with equal batch and matching contract dims. -/
private lemma batch_matrix_matrix
  [Semifield α]
-- given
  (A : Tensor α (bz ++ [m, k]))
  (C : Tensor α (bz ++ [k, n]))
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  let A_div0 : Tensor α (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor α) (by simp [InsertIdxAppend.eq.Append_InsertIdx]))
      ((A / B).unsqueeze (bz.length + 1))
  let A0 : Tensor α (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor α) (by simp [InsertIdxAppend.eq.Append_InsertIdx]))
      (A.unsqueeze (bz.length + 1))
  have h0 : A_div0 = A0 / B := by
    simp only [A_div0, A0]
    have hu := unsqueeze_div A B (bz.length + 1)
    rw [hu]
    exact cast_div (by simp [InsertIdxAppend.eq.Append_InsertIdx]) (A.unsqueeze (bz.length + 1)) B
  let A_div : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨bz.length + 1, by grind⟩ n)
  let A' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨bz.length + 1, by grind⟩ n)
  let CT : Tensor α (bz ++ [n, k]) :=
    cast (congrArg (Tensor α) (by
      rw [SwapAppend.eq.Append_Swap.of.LeLength.LeLength (by simp) (by simp)]
      simp [EqSwap_0'1])) Cᵀ
  let C0 : Tensor α (bz ++ [1, n, k]) :=
    cast (congrArg (Tensor α) (by simp [InsertIdxAppend.eq.Append_Cons]))
      (CT.unsqueeze bz.length)
  let C' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨bz.length, by grind⟩ m)
  have hA : A_div = A' / B := by
    simp only [A_div, A']
    rw [h0, repeat_div A0 B ⟨bz.length + 1, by grind⟩ n]
    exact cast_div (by simp) _ B
  have hL : (A / B) @ C ≃ (A_div * C').sum (bz.length + 2) := by
    simpa [A_div, A_div0, C', C0, CT] using Dot.as.SumMul (A / B) C
  have hR : A @ C ≃ (A' * C').sum (bz.length + 2) := by
    simpa [A', A0, C', C0, CT] using Dot.as.SumMul A C
  have hsum : (A_div * C').sum (bz.length + 2) =
      (A' * C').sum (bz.length + 2) / B := by
    rw [hA, mul_div_tensor, SumDiv.eq.DivSum]
  have hs : matmul_shape (bz ++ [m, k]) (bz ++ [k, n]) =
      (bz ++ [m, n, k]).eraseIdx (bz.length + 2) := hL.left
  have hL_eq : (A / B) @ C =
      cast (congrArg (Tensor α) hs.symm)
        ((A_div * C').sum (bz.length + 2)) := SEq.cast.comm hL
  have hR_eq : A @ C =
      cast (congrArg (Tensor α) hs.symm)
        ((A' * C').sum (bz.length + 2)) := SEq.cast.comm hR
  rw [hL_eq, hR_eq, hsum]
  exact CastDiv.eq.DivCast.of.Eq.scalar hs.symm ((A' * C').sum (bz.length + 2)) B


/-- `bmm` distributes over scalar division. -/
private lemma bmm_div
  [Semifield α]
-- given
  (A : Tensor α (bz ++ [m, k]))
  (C : Tensor α (bz ++ [k, n]))
  (B : Tensor α []) :
-- imply
  (A / B).bmm C = A.bmm C / B := by
-- proof
  let A_div0 : Tensor α (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor α) (by simp [InsertIdxAppend.eq.Append_InsertIdx]))
      ((A / B).unsqueeze (bz.length + 1))
  let A0 : Tensor α (bz ++ [m, 1, k]) :=
    cast (congrArg (Tensor α) (by simp [InsertIdxAppend.eq.Append_InsertIdx]))
      (A.unsqueeze (bz.length + 1))
  have h0 : A_div0 = A0 / B := by
    simp only [A_div0, A0]
    have hu := unsqueeze_div A B (bz.length + 1)
    rw [hu]
    exact cast_div (by simp [InsertIdxAppend.eq.Append_InsertIdx]) (A.unsqueeze (bz.length + 1)) B
  let A_div : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (A_div0.repeat ⟨bz.length + 1, by grind⟩ n)
  let A' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (A0.repeat ⟨bz.length + 1, by grind⟩ n)
  let CT : Tensor α (bz ++ [n, k]) :=
    cast (congrArg (Tensor α) (by
      rw [SwapAppend.eq.Append_Swap.of.LeLength.LeLength (by simp) (by simp)]
      simp [EqSwap_0'1])) Cᵀ
  let C0 : Tensor α (bz ++ [1, n, k]) :=
    cast (congrArg (Tensor α) (by
      rw [InsertIdxAppend.eq.Append_InsertIdx.of.LeLength (by simp)]
      simp))
      (CT.unsqueeze bz.length)
  let C' : Tensor α (bz ++ [m, n, k]) :=
    cast (congrArg (Tensor α) (by simp)) (C0.repeat ⟨bz.length, by grind⟩ m)
  have hA : A_div = A' / B := by
    simp only [A_div, A']
    rw [h0, repeat_div A0 B ⟨bz.length + 1, by grind⟩ n]
    exact cast_div (by simp) _ B
  have hsum : (A_div * C').sum (bz.length + 2) =
      (A' * C').sum (bz.length + 2) / B := by
    rw [hA, mul_div_tensor, SumDiv.eq.DivSum]
  have hs :
      (bz ++ [m, n, k]).eraseIdx (bz.length + 2) = bz ++ [m, n] := by
    simp [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength]
  have hL : (A / B).bmm C =
      cast (congrArg (Tensor α) hs)
        ((A_div * C').sum (bz.length + 2)) := by
    simp [Tensor.bmm, A_div, A_div0, C', C0, CT]
  have hR : A.bmm C =
      cast (congrArg (Tensor α) hs)
        ((A' * C').sum (bz.length + 2)) := by
    simp [Tensor.bmm, A', A0, C', C0, CT]
  rw [hL, hR, hsum]
  exact CastDiv.eq.DivCast.of.Eq.scalar hs ((A' * C').sum (bz.length + 2)) B


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
      apply Eq.of.SEq
      exact hL.trans (SEq.of.Eq (bmm_div A C B)) |>.trans
        (SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
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
        rw [SetAppend.eq.Append_Set.of.GtLength (by simp)]
        simp [Set_0.eq.Cons_Tail.of.GtLength_0]
      have hcastC :
          ((n' :: s') ++ [t, k]).set 0 (n ⊔ n') = (n ⊔ n' :: s') ++ [t, k] := by
        rw [SetAppend.eq.Append_Set.of.GtLength (by simp)]
        simp [Set_0.eq.Cons_Tail.of.GtLength_0]
      let Ar : Tensor α ((n ⊔ n' :: s) ++ [m, t]) :=
        cast (congrArg (Tensor α) hcastA) (A.resize ⟨0, by grind⟩ (n ⊔ n'))
      let Adr : Tensor α ((n ⊔ n' :: s) ++ [m, t]) :=
        cast (congrArg (Tensor α) hcastA) ((A / B).resize ⟨0, by grind⟩ (n ⊔ n'))
      let Cr : Tensor α ((n ⊔ n' :: s') ++ [t, k]) :=
        cast (congrArg (Tensor α) hcastC) (C.resize ⟨0, by grind⟩ (n ⊔ n'))
      have hAdr : Adr = Ar / B := by
        simp only [Adr, Ar]
        rw [resize_div A B ⟨0, by grind⟩ (n ⊔ n')]
        exact cast_div hcastA _ B
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
          apply Eq.of.SEq
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
            (SEqUFnS.of.SEq hgetR.symm
              (fun (t : Tensor α _) => (t / B : Tensor α _))) |>.trans
            (SEqUFnS.of.SEq hCR
              (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
          refine
            (SEqMatmulS.of.SEq.SEq (by simpa using hlen')
              ((GetCast.as.Get.of.Eq.GtLength_0.right.fin
                  (by simp) hXA (Ar / B) i).trans (SEq.of.Eq hAi))
              (GetCast.as.Get.of.Eq.GtLength_0.right.fin
                  (by simp) hYA Cr i)).trans
              (SEq.of.Eq ih')
        apply Eq.of.SEq
        refine (SEqCast.of.Eq hshape
            ((Ar / B).matmul Cr (by simpa using hlen'))).symm.trans ?_
        exact (SEq.of.Eq hLR).trans
          (SEqUFnS.of.SEq (SEqCast.of.Eq hshape
              (Ar.matmul Cr (by simpa using hlen')))
            (fun (t : Tensor α _) => (t / B : Tensor α _)))

      apply Eq.of.SEq
      refine hL.trans ?_
      have hmid := SEq.of.Eq hmat
      simpa [Adr, Ar, Cr] using
        hmid.trans (SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


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


/-- Length-1 unequal-batch `matmul`. -/
private lemma matmul_div_len1
  [Semifield α]
-- given
  (A : Tensor α ([b] ++ [m, t]))
  (C : Tensor α ([b'] ++ [t, k]))
  (B : Tensor α []) :
-- imply
  (A / B).matmul C (by simp) = A.matmul C (by simp) / B :=
-- proof
  matmul_div_eq_len (by simp) A C B


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
  apply Eq.of.SEq
  let batch := s.take (s.length - 2)
  let batch' := s'.take (s'.length - 2)
  let m := s[s.length - 2]
  let n := s[s.length - 1]
  let n' := s'[s'.length - 2]
  let k := s'[s'.length - 1]
  let K := n ⊔ n'
  let X0 : Tensor α (batch ++ [m, n]) :=
    cast (congrArg (Tensor α) (EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
  let Xd0 : Tensor α (batch ++ [m, n]) :=
    cast (congrArg (Tensor α) (EqAppendTake__ListGet.of.GeLength_2 hs).symm) (A / B)
  have hXd0 : Xd0 = X0 / B :=
    cast_div (EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
  let X : Tensor α (batch ++ [m, K]) :=
    cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ K)
  let Xd : Tensor α (batch ++ [m, K]) :=
    cast (by simp) (Xd0.resize ⟨batch.length + 1, by grind⟩ K)
  have hXd : Xd = X / B := by
    simp only [Xd, X, hXd0]
    rw [resize_div X0 B ⟨batch.length + 1, by grind⟩ K]
    exact cast_div (by simp) _ B
  let Y0 : Tensor α (batch' ++ [n', k]) :=
    cast (congrArg (Tensor α) (EqAppendTake__ListGet.of.GeLength_2 hs').symm) C
  let Y' : Tensor α (batch' ++ [K, k]) :=
    cast (by simp) (Y0.resize ⟨batch'.length, by grind⟩ K)
  have hbY : batch' ++ [K, k] = batch ++ [K, k] := by
    simp only [batch, batch']; rw [hb]
  let Y : Tensor α (batch ++ [K, k]) :=
    cast (congrArg (Tensor α) hbY) Y'
  have hY : Y' ≃ Y := (SEqCast.of.Eq hbY Y').symm
  have htd : Xd.tensordot Y = X.tensordot Y / B := by
    rw [hXd]; exact tensordot_div_same X Y B
  have htd' : Xd.tensordot Y' = X.tensordot Y' / B := by
    apply Eq.of.SEq
    have h1 :=
      SEqTensordotS.of.SEq.SEq.Eq.Eq (by rfl) (by rfl) (by rfl : Xd ≃ Xd) hY
    have h2 :=
      SEqTensordotS.of.SEq.SEq.Eq.Eq (by rfl) (by rfl) (by rfl : X ≃ X) hY
    exact h1.trans (SEq.of.Eq htd) |>.trans
      (SEqUFnS.of.SEq h2.symm (fun (t : Tensor α _) => (t / B : Tensor α _)))
  have hL : (A / B).einsum C ≃ Xd.tensordot Y' := by
    refine hEd.trans ?_
    simp only [Xd, Xd0, Y', Y0, batch, batch', m, n, n', k, K]
    rfl
  have hR : A.einsum C ≃ X.tensordot Y' := by
    refine hE.trans ?_
    simp only [X, X0, Y', Y0, batch, batch', m, n, n', k, K]
    rfl
  exact hL.trans (SEq.of.Eq htd') |>.trans
    (SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


/-- Rank-3 any leading/contract dims. -/
private lemma rank3_any
  [Semifield α]
-- given
  (A : Tensor α [b, m, k])
  (C : Tensor α [b', k', n])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  if hb : b = b' then
    subst hb
    exact both_ge_2 (by simp) (by simp) (by simp) A C B
  else
    simp only [Dot.dot]
    have hE := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 (by simp) (by simp) A C
    have hEd := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 (by simp) (by simp) (A / B) C
    let K := k ⊔ k'
    let X : Tensor α ([b] ++ [m, K]) :=
      cast (by simp) (A.resize ⟨2, by grind⟩ K)
    let Xd : Tensor α ([b] ++ [m, K]) :=
      cast (by simp) ((A / B).resize ⟨2, by grind⟩ K)
    let Y : Tensor α ([b'] ++ [K, n]) :=
      cast (by simp) (C.resize ⟨1, by grind⟩ K)
    have hXd : Xd = X / B := by
      simp only [Xd, X]
      rw [resize_div A B ⟨2, by grind⟩ K]
      exact cast_div (by simp) _ B
    have htd : Xd.tensordot Y = X.tensordot Y / B := by
      have h1 := Tensordot.eq.Matmul.of.Length (by simp) Xd Y
      have h2 := Tensordot.eq.Matmul.of.Length (by simp) X Y
      rw [h1, h2, hXd]
      exact matmul_div_len1 (b := b) (b' := b') X Y B
    apply Eq.of.SEq
    have hL : (A / B).einsum C ≃ Xd.tensordot Y := by
      refine hEd.trans ?_
      simp only [Xd, Y, K]
      rfl
    have hR : A.einsum C ≃ X.tensordot Y := by
      refine hE.trans ?_
      simp only [X, Y, K]
      rfl
    exact hL.trans (SEq.of.Eq htd) |>.trans
      (SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


/-- Vector @ rank ≥ 2. -/
private lemma vector_ge2
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
    apply Eq.of.SEq
    let batch := s'.take (s'.length - 2)
    let k := s'[s'.length - 1]
    let Y' : Tensor α (batch ++ [n, k]) :=
      cast (congrArg (Tensor α) (by
        simp only [batch, k]
        rw [h_eq]
        exact (EqAppendTake__ListGet.of.GeLength_2 hs').symm)) C
    let X' := A.reshape (batch ++ [1, n]) (by simp)
    let Xd := (A / B).reshape (batch ++ [1, n]) (by simp)
    have hx : Xd = X' / B := reshape_div A B _ _
    have hbmm : Xd.bmm Y' = X'.bmm Y' / B := by
      rw [hx]; exact bmm_div X' Y' B
    have hsel :
        (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ =
          (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]; exact select_div (X'.bmm Y') B _ _
    have hL : (A / B).einsum C ≃
        (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xd, Y', batch, k]
      rfl
    have hR : A.einsum C ≃
        (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X', Y', batch, k]
      rfl
    exact hL.trans (SEq.of.Eq hsel) |>.trans
      (SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else if hgt : n > s'[s'.length - 2] then
    have hE := Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2 hs' hgt A C
    have hEd := Einsum.as.SelectBmm.of.Gt_Get_SubLength.GeLength_2 hs' hgt (A / B) C
    apply Eq.of.SEq
    let batch := s'.take (s'.length - 2)
    let n₀ := s'[s'.length - 2]
    let k' := s'[s'.length - 1]
    let Y0 : Tensor α (batch ++ [n₀, k']) :=
      cast (congrArg (Tensor α) (EqAppendTake__ListGet.of.GeLength_2 hs').symm) C
    let Y' : Tensor α (batch ++ [n, k']) :=
      cast (by simp) (Y0.resize ⟨batch.length, by grind⟩ n)
    let X' := A.reshape (batch ++ [1, n]) (by simp)
    let Xd := (A / B).reshape (batch ++ [1, n]) (by simp)
    have hx : Xd = X' / B := reshape_div A B _ _
    have hbmm : Xd.bmm Y' = X'.bmm Y' / B := by
      rw [hx]; exact bmm_div X' Y' B
    have hsel :
        (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ =
          (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]; exact select_div (X'.bmm Y') B _ _
    have hL : (A / B).einsum C ≃
        (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xd, Y', Y0, batch, n₀, k']
      rfl
    have hR : A.einsum C ≃
        (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X', Y', Y0, batch, n₀, k']
      rfl
    exact hL.trans (SEq.of.Eq hsel) |>.trans
      (SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else
    have hlt : n < s'[s'.length - 2] := Nat.lt_of_le_of_ne (le_of_not_gt hgt) h_eq
    have hE := Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2 hs' hlt A C
    have hEd := Einsum.as.SelectBmm.of.GtGet_SubLength.GeLength_2 hs' hlt (A / B) C
    apply Eq.of.SEq
    let batch := s'.take (s'.length - 2)
    let n₀ := s'[s'.length - 2]
    let k' := s'[s'.length - 1]
    let Y' : Tensor α (batch ++ [n₀, k']) :=
      cast (congrArg (Tensor α) (by
        simp only [batch, n₀, k']
        exact (EqAppendTake__ListGet.of.GeLength_2 hs').symm)) C
    let A_r : Tensor α [n₀] := cast (by simp) (A.resize ⟨0, by grind⟩ n₀)
    let Ad_r : Tensor α [n₀] := cast (by simp) ((A / B).resize ⟨0, by grind⟩ n₀)
    have hr : Ad_r = A_r / B := by
      simp only [Ad_r, A_r]
      rw [resize_div A B ⟨0, by grind⟩ n₀]
      exact cast_div (by simp) _ B
    let X' := A_r.reshape (batch ++ [1, n₀]) (by simp)
    let Xd := Ad_r.reshape (batch ++ [1, n₀]) (by simp)
    have hx : Xd = X' / B := by
      simp only [Xd, X', hr]
      exact reshape_div A_r B (batch ++ [1, n₀]) (by simp)
    have hbmm : Xd.bmm Y' = X'.bmm Y' / B := by
      rw [hx]; exact bmm_div X' Y' B
    have hsel :
        (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ =
          (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]; exact select_div (X'.bmm Y') B _ _
    have hL : (A / B).einsum C ≃
        (Xd.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xd, Y', Ad_r, batch, n₀, k']
      rfl
    have hR : A.einsum C ≃
        (X'.bmm Y').select ⟨s'.length - 2, by simp [batch]⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X', Y', A_r, batch, n₀, k']
      rfl
    exact hL.trans (SEq.of.Eq hsel) |>.trans
      (SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


/-- Rank ≥ 2 @ vector. -/
private lemma ge2_vector
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
  if h_eq : s[s.length - 1] = n' then
    have hE := Einsum.as.SelectBmm.of.EqGet_SubLength_1.GeLength_2 hs h_eq A C
    have hEd := Einsum.as.SelectBmm.of.EqGet_SubLength_1.GeLength_2 hs h_eq (A / B) C
    apply Eq.of.SEq
    let batch := s.take (s.length - 2)
    let k := s[s.length - 2]
    let n := s[s.length - 1]
    let X0 : Tensor α (batch ++ [k, n]) :=
      cast (congrArg (Tensor α) (EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
    let Xd0 : Tensor α (batch ++ [k, n]) :=
      cast (congrArg (Tensor α) (EqAppendTake__ListGet.of.GeLength_2 hs).symm) (A / B)
    have hx0 : Xd0 = X0 / B :=
      cast_div (EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
    let Y' := C.reshape (batch ++ [n, 1]) (by simp_all [n])
    have hbmm : Xd0.bmm Y' = X0.bmm Y' / B := by
      rw [hx0]; exact bmm_div X0 Y' B
    have hsel :
        (Xd0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ =
          (X0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]; exact select_div (X0.bmm Y') B _ _
    have hL : (A / B).einsum C ≃
        (Xd0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xd0, Y', batch, k, n]
      rfl
    have hR : A.einsum C ≃
        (X0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X0, Y', batch, k, n]
      rfl
    exact hL.trans (SEq.of.Eq hsel) |>.trans
      (SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else if hge : s[s.length - 1] ≥ n' then
    have hE := Einsum.as.SelectBmm.of.GeGet_SubLength_1.GeLength_2 hs hge A C
    have hEd := Einsum.as.SelectBmm.of.GeGet_SubLength_1.GeLength_2 hs hge (A / B) C
    apply Eq.of.SEq
    let batch := s.take (s.length - 2)
    let k := s[s.length - 2]
    let n := s[s.length - 1]
    let X0 : Tensor α (batch ++ [k, n]) :=
      cast (congrArg (Tensor α) (EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
    let Xd0 : Tensor α (batch ++ [k, n]) :=
      cast (congrArg (Tensor α) (EqAppendTake__ListGet.of.GeLength_2 hs).symm) (A / B)
    have hx0 : Xd0 = X0 / B :=
      cast_div (EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
    let Cr : Tensor α [n] := cast (by simp) (C.resize ⟨0, by grind⟩ n)
    let Y' := Cr.reshape (batch ++ [n, 1]) (by simp)
    have hbmm : Xd0.bmm Y' = X0.bmm Y' / B := by
      rw [hx0]; exact bmm_div X0 Y' B
    have hsel :
        (Xd0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ =
          (X0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]; exact select_div (X0.bmm Y') B _ _
    have hL : (A / B).einsum C ≃
        (Xd0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xd0, Y', Cr, batch, k, n]
      rfl
    have hR : A.einsum C ≃
        (X0.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [X0, Y', Cr, batch, k, n]
      rfl
    exact hL.trans (SEq.of.Eq hsel) |>.trans
      (SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else
    have hlt : s[s.length - 1] < n' := Nat.lt_of_not_ge hge
    have hE := Einsum.as.SelectBmm.of.LtGet_SubLength_1.GeLength_2 hs hlt A C
    have hEd := Einsum.as.SelectBmm.of.LtGet_SubLength_1.GeLength_2 hs hlt (A / B) C
    apply Eq.of.SEq
    let batch := s.take (s.length - 2)
    let k := s[s.length - 2]
    let n := s[s.length - 1]
    let X0 : Tensor α (batch ++ [k, n]) :=
      cast (congrArg (Tensor α) (EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
    let Xd0 : Tensor α (batch ++ [k, n]) :=
      cast (congrArg (Tensor α) (EqAppendTake__ListGet.of.GeLength_2 hs).symm) (A / B)
    have hx0 : Xd0 = X0 / B :=
      cast_div (EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
    let Xr : Tensor α (batch ++ [k, n']) :=
      cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ n')
    let Xdr : Tensor α (batch ++ [k, n']) :=
      cast (by simp) (Xd0.resize ⟨batch.length + 1, by grind⟩ n')
    have hxr : Xdr = Xr / B := by
      simp only [Xdr, Xr, hx0]
      rw [resize_div X0 B ⟨batch.length + 1, by grind⟩ n']
      exact cast_div (by simp) _ B
    let Y' := C.reshape (batch ++ [n', 1]) (by simp)
    have hbmm : Xdr.bmm Y' = Xr.bmm Y' / B := by
      rw [hxr]; exact bmm_div Xr Y' B
    have hsel :
        (Xdr.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ =
          (Xr.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ / B := by
      rw [hbmm]; exact select_div (Xr.bmm Y') B _ _
    have hL : (A / B).einsum C ≃
        (Xdr.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
      refine hEd.trans ?_
      simp only [Xdr, Xd0, Y', batch, k, n]
      rfl
    have hR : A.einsum C ≃
        (Xr.bmm Y').select ⟨s.length - 1, by simp [batch]; omega⟩ ⟨0, by grind⟩ := by
      refine hE.trans ?_
      simp only [Xr, X0, Y', batch, k, n]
      rfl
    exact hL.trans (SEq.of.Eq hsel) |>.trans
      (SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


/-- Arbitrary-batch `tensordot` distributes over scalar division. -/
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
    have hdvd : (s ++ [m, n]).prod ∣ sR.prod := by
      have hsR : sR = s'.take (s'.length - s.length) ++ (s ++ [m, n]) := by
        dsimp [sR]; exact List.append_assoc _ _ _
      rw [hsR]
      conv => rhs; rw [List.prod_append]
      exact Nat.dvd_mul_left _ _
    have hr : (A / B).reshape sR hdvd = A.reshape sR hdvd / B :=
      reshape_div A B sR hdvd
    have hmat :=
      matmul_div_eq_len (by grind) (A.reshape sR hdvd) C B
    apply Eq.of.SEq
    refine hL.trans ?_
    -- `hL`/`hR` use `(by simp)` dvd proofs; align via convert/proof-irrel
    convert (SEq.of.Eq (by
      have hmat' : ((A / B).reshape sR hdvd).matmul C (by grind) =
          (A.reshape sR hdvd).matmul C (by grind) / B := by
        rw [hr]; exact hmat
      exact hmat')).trans
      (SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else if hgt : s.length > s'.length then
    have hge : s.length ≥ s'.length := Nat.le_of_lt hgt
    have hL := Tensordot.as.Matmul.of.GeLengthS hge (A / B) C
    have hR := Tensordot.as.Matmul.of.GeLengthS hge A C
    let sL := s.take (s.length - s'.length) ++ s' ++ [n, k]
    have hdvd : (s' ++ [n, k]).prod ∣ sL.prod := by
      have hsL : sL = s.take (s.length - s'.length) ++ (s' ++ [n, k]) := by
        dsimp [sL]; exact List.append_assoc _ _ _
      rw [hsL]
      conv => rhs; rw [List.prod_append]
      exact Nat.dvd_mul_left _ _
    have hmat' :=
      matmul_div_eq_len (by grind) A (C.reshape sL hdvd) B
    apply Eq.of.SEq
    refine hL.trans ?_
    convert (SEq.of.Eq hmat').trans
      (SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm
  else
    have hlen : s.length = s'.length :=
      Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
    have h1 := Tensordot.eq.Matmul.of.Length hlen (A / B) C
    have h2 := Tensordot.eq.Matmul.of.Length hlen A C
    rw [h1, h2]
    exact matmul_div_eq_len hlen A C B


/-- Both ranks ≥ 2, possibly unequal batch prefixes. -/
private lemma both_ge_2_any
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
    exact both_ge_2 hs hs' hb A C B
  else
    simp only [Dot.dot]
    have hE := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' A C
    have hEd := Einsum.as.Tensordot.of.GeLength_2.GeLength_2 hs hs' (A / B) C
    apply Eq.of.SEq
    let batch := s.take (s.length - 2)
    let batch' := s'.take (s'.length - 2)
    let m := s[s.length - 2]
    let n := s[s.length - 1]
    let n' := s'[s'.length - 2]
    let k := s'[s'.length - 1]
    let K := n ⊔ n'
    let X0 : Tensor α (batch ++ [m, n]) :=
      cast (congrArg (Tensor α) (EqAppendTake__ListGet.of.GeLength_2 hs).symm) A
    let Xd0 : Tensor α (batch ++ [m, n]) :=
      cast (congrArg (Tensor α) (EqAppendTake__ListGet.of.GeLength_2 hs).symm) (A / B)
    have hXd0 : Xd0 = X0 / B :=
      cast_div (EqAppendTake__ListGet.of.GeLength_2 hs).symm A B
    let X : Tensor α (batch ++ [m, K]) :=
      cast (by simp) (X0.resize ⟨batch.length + 1, by grind⟩ K)
    let Xd : Tensor α (batch ++ [m, K]) :=
      cast (by simp) (Xd0.resize ⟨batch.length + 1, by grind⟩ K)
    have hXd : Xd = X / B := by
      simp only [Xd, X, hXd0]
      rw [resize_div X0 B ⟨batch.length + 1, by grind⟩ K]
      exact cast_div (by simp) _ B
    let Y0 : Tensor α (batch' ++ [n', k]) :=
      cast (congrArg (Tensor α) (EqAppendTake__ListGet.of.GeLength_2 hs').symm) C
    let Y' : Tensor α (batch' ++ [K, k]) :=
      cast (by simp) (Y0.resize ⟨batch'.length, by grind⟩ K)
    have htd : Xd.tensordot Y' = X.tensordot Y' / B := by
      rw [hXd]; exact tensordot_div X Y' B
    have hL : (A / B).einsum C ≃ Xd.tensordot Y' := by
      refine hEd.trans ?_
      simp only [Xd, Xd0, Y', Y0, batch, batch', m, n, n', k, K]
      rfl
    have hR : A.einsum C ≃ X.tensordot Y' := by
      refine hE.trans ?_
      simp only [X, X0, Y', Y0, batch, batch', m, n, n', k, K]
      rfl
    exact hL.trans (SEq.of.Eq htd) |>.trans
      (SEqUFnS.of.SEq hR (fun (t : Tensor α _) => (t / B : Tensor α _))).symm


/-- Tensor-scalar form: division by a 0-dimensional tensor. -/
@[main]
private lemma main
  [Semifield α]
-- given
  (A : Tensor α s)
  (B : Tensor α [])
  (C : Tensor α s') :
-- imply
  (A / B) @ C = A @ C / B := by
-- proof
  match s, s' with
  | [], _ =>
    exact left_nil A B C
  | _ :: _, [] =>
    exact right_nil A B C
  | [n], [n'] =>
    exact vector_vector_any A C B
  | [n], [k, d] =>
    exact vector_matrix A C B
  | [m, k], [d] =>
    exact matrix_vector A C B
  | [m, k], [k', n] =>
    exact matrix_matrix_any A C B
  | [b, m, k], [b', k', n] =>
    exact rank3_any A C B
  | n :: rest, s' =>
    if hboth : (n :: rest).length ≥ 2 ∧ s'.length ≥ 2 then
      exact both_ge_2_any hboth.1 hboth.2 A C B
    else if hvec : (n :: rest).length = 1 ∧ s'.length ≥ 2 then
      have hn : rest = [] := by
        have := hvec.1
        cases rest <;> simp_all
      subst hn
      exact vector_ge2 hvec.2 A C B
    else if hleft : (n :: rest).length ≥ 2 ∧ s'.length = 1 then
      match s' with
      | [] =>
        simp at hleft
      | d :: t =>
        have ht : t = [] := by
          have := hleft.2
          cases t <;> simp_all
        subst ht
        exact ge2_vector hleft.1 A C B
    else
      cases s' with
      | nil =>
        exact right_nil A B C
      | cons _ t =>
        have ht : t = [] := by
          have := hboth; have := hvec; have := hleft
          cases t <;> simp_all
        subst ht
        have hn : rest = [] := by
          have := hboth; have := hvec; have := hleft
          cases rest <;> simp_all
        subst hn
        exact vector_vector_any A C B


-- created on 2026-08-11
-- updated on 2026-08-12
