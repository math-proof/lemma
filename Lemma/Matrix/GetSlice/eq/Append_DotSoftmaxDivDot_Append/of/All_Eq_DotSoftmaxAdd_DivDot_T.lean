import Lemma.Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T
import Def.LinearAlgebra.Matrix.ToTensor
import Def.LinearAlgebra.Matrix.BandPart
import Def.Analysis.Matrix.Softmax
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.DataStack.eq.FlattenMap_FunData
import Lemma.Tensor.Softmax.eq.TensorSoftmaxData
import Lemma.Vector.EqGetRange
import Lemma.Tensor.EqGet1_1
import Lemma.Tensor.EqItem1'1
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.GetFlatten.eq.Get.of.Lt_Mul
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Vector.GetExp.eq.ExpGet
import Lemma.Vector.Sum.eq.Sum_Get
import Lemma.Vector.Softmax.eq.Div_SumExp
import Lemma.Tensor.GetSoftmax.eq.SoftmaxGet.of.GtGet_0.LtAdd_1Length
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Tensor.XEq.is.All_XEqGetS
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Vector.XEq.is.All_XEqGetS
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.MapStack.eq.Stack_Map
import Lemma.Tensor.XEq.of.Eq
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetGetSlice.eq.Get_Add.of.GtSubMin
import Lemma.List.LengthSlice.eq.SubMin
import Instance.LinearAlgebra.Matrix.IsClose
import Lemma.Tensor.EqGetT
import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Tensor.GetDiv.eq.DivGet
import Lemma.Tensor.GetMul.eq.MulGet
import Lemma.Tensor.BandPart.eq.Stack_BoolIn_Icc
import Lemma.Tensor.GetNeg.eq.NegGet
import Lemma.Tensor.ItemNeg.eq.NegItem
import Lemma.List.EqSwap_0'1
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
open Tensor Matrix Bool Exp
open List (EqSwap_0'1)
open Vector (EqGetRange)
set_option maxHeartbeats 800000


private lemma item_coe
-- given
  (x : α) :
-- imply
  (x : Tensor α []).item = x
  := by
-- proof
  unfold Tensor.item
  change ([x] : List α)[0]'(by simp) = x
  simp

private lemma stack_get
  {n : ℕ}
-- given
  (x : Fin n → α)
  (j : Fin n) :
-- imply
  (([k < n] (x k : Tensor α [])).data).get ⟨j, by simp⟩ = x j
  := by
-- proof
  rw [DataStack.eq.FlattenMap_FunData.fin]
  have h_t : (j : ℕ) < n * [].prod := by simp
  have hflat := Vector.GetFlatten.eq.Get.of.Lt_Mul h_t
    ((List.Vector.range n).map fun i => ((x i : Tensor α []).data))
  simp [Nat.mod_one] at hflat
  erw [hflat]
  erw [Vector.GetMap.eq.UFnGet.fin]
  have hr := Vector.EqGetRange.fin j
  erw [hr]
  simp [List.Vector.head]

private lemma mk_stack
  {n : ℕ}
-- given
  (v : List.Vector α [n].prod) :
-- imply
  (⟨v⟩ : Tensor α [n]) = [j < n] ((v.get ⟨j, by simp⟩) : Tensor α [])
  := by
-- proof
  apply Eq.of.EqDataS
  symm
  apply Vector.Eq.of.All_EqGetS.fin
  intro j
  have hj : (j : ℕ) < n := by simpa using j.isLt
  simp
  erw [stack_get (fun i => v.get ⟨i, by simp⟩) ⟨j, hj⟩]
  apply congrArg v.get
  exact Fin.ext (by rfl)

private lemma stack_softmax_item
  {n : ℕ}
-- given
  (x : Fin n → ℝ*)
  (j : Fin n) :
-- imply
  ((([k < n] (x k : Tensor ℝ* [])).softmax).get ⟨j, by simp [Tensor.length]⟩).item
    = Exp.exp (x j) / ∑ k : Fin n, Exp.exp (x k)
  := by
-- proof
  rw [Softmax.eq.TensorSoftmaxData]
  rw [mk_stack (([k < n] (x k : Tensor ℝ* [])).data.softmax)]
  have hget := EqGetStack.fin
    (fun t : Fin n =>
      (((( [k < n] (x k : Tensor ℝ* [])).data.softmax).get ⟨t, by simp⟩) : Tensor ℝ* []))
    j
  simp at hget
  erw [hget]
  erw [item_coe (((( [k < n] (x k : Tensor ℝ* [])).data.softmax).get ⟨j, by simp⟩))]
  rw [Vector.Softmax.eq.Div_SumExp]
  rw [Vector.GetDiv.eq.DivGet.fin]
  rw [Vector.GetExp.eq.ExpGet.fin]
  congr 1
  · exact congrArg Exp.exp (stack_get x j)
  ·
    rw [Vector.Sum.eq.Sum_Get.fin]
    let e : Fin n ≃ Fin [n].prod :=
      { toFun i := ⟨i, by simp⟩
        invFun i := ⟨i.val, by simpa using i.isLt⟩
        left_inv := by intro i; exact Fin.ext rfl
        right_inv := by intro i; exact Fin.ext rfl }
    rw [← e.sum_comp
      (fun i : Fin [n].prod => (Exp.exp (([k < n] (x k : Tensor ℝ* [])).data)).get i)]
    apply Finset.sum_congr rfl
    intro k _
    rw [Vector.GetExp.eq.ExpGet.fin]
    exact congrArg Exp.exp (stack_get x k)

private lemma mat_softmax_item
  {m n : ℕ}
-- given
  (A : Matrix (Fin m) (Fin n) ℝ*)
  (i : Fin m)
  (j : Fin n) :
-- imply
  ((((A.toTensor).softmax 1).get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩).item
    = (A.softmax 1) i j
  := by
-- proof
  have hrow := GetSoftmax.eq.SoftmaxGet.of.GtGet_0.LtAdd_1Length (s := [m, n]) (d := 0)
    (by simp) i.isLt A.toTensor
  simp [GetElem.getElem] at hrow
  erw [hrow]
  unfold Matrix.toTensor
  have hstack := EqGetStack.fin (fun r : Fin m => [c < n] (A r c : Tensor ℝ* [])) i
  simp at hstack
  erw [hstack]
  erw [stack_softmax_item (fun c => A i c) j]
  unfold Matrix.softmax
  simp [Matrix.of_apply]

private lemma toTensor_get
  {m n : ℕ}
-- given
  (A : Matrix (Fin m) (Fin n) α)
  (i : Fin m)
  (j : Fin n) :
-- imply
  (A.toTensor)[i][j] = (A i j : Tensor α [])
  := by
-- proof
  unfold Matrix.toTensor
  have hrow := EqGetStack.fin (fun i : Fin m => [j < n] (A i j : Tensor α [])) i
  have hcol := EqGetStack.fin (fun j : Fin n => (A i j : Tensor α [])) j
  simp [GetElem.getElem] at hrow hcol ⊢
  erw [hrow, hcol]

private lemma toTensor_get'
  {m n : ℕ}
-- given
  (A : Matrix (Fin m) (Fin n) α)
  (i : Fin m)
  (j : Fin n) :
-- imply
  (A.toTensor.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩
    = (A i j : Tensor α [])
  := by
-- proof
  simpa [GetElem.getElem] using toTensor_get A i j

private lemma item_add
  [Add α]
-- given
  (a b : Tensor α []) :
-- imply
  (Add.add a b).item = a.item + b.item
  := by
-- proof
  simp [Tensor.item, Add.add]
  exact Vector.GetAdd.eq.AddGetS.fin a.data b.data ⟨0, Nat.zero_lt_one⟩

private lemma item_sum
  [AddCommMonoid α]
  {n : ℕ}
-- given
  (f : Fin n → Tensor α []) :
-- imply
  (∑ i : Fin n, f i).item = ∑ i : Fin n, (f i).item
  := by
-- proof
  induction n with
  | zero =>
    simp
    unfold Tensor.item
    rfl
  | succ n ih =>
    simp only [Fin.sum_univ_castSucc]
    erw [item_add, ih]

private lemma item_hmul
  [Mul α]
-- given
  (a b : Tensor α []) :
-- imply
  (a * b).item = a.item * b.item
  := by
-- proof
  simp [Tensor.item, HMul.hMul]
  change (a.data.map (fun x => x * b.data[0])).get ⟨0, Nat.zero_lt_one⟩ =
    a.data.get ⟨0, Nat.zero_lt_one⟩ * b.data[0]
  erw [Vector.GetMap.eq.UFnGet.fin a.data (fun x => x * b.data[0]) ⟨0, Nat.zero_lt_one⟩]

private lemma dot_item
  {m k n : ℕ}
-- given
  (A : Matrix (Fin m) (Fin k) ℝ*)
  (B : Matrix (Fin k) (Fin n) ℝ*)
  (i : Fin m)
  (j : Fin n) :
-- imply
  (A.toTensor @ B.toTensor)[i, j].item = ∑ t : Fin k, A i t * B t j
  := by
-- proof
  convert congrArg Tensor.item (GetDot.eq.Sum_MulGetS.fin A.toTensor B.toTensor i j) using 1
  · rfl
  ·
    rw [item_sum]
    refine Finset.sum_congr rfl ?_
    intro t _
    have ha := toTensor_get' A i t
    have hb := toTensor_get' B t j
    erw [ha, hb]
    erw [item_hmul]
    simp [id]
    erw [item_coe (A i t), item_coe (B t j)]

private lemma item_hadd
-- given
  (a b : Tensor ℝ* []) :
-- imply
  (a + b).item = a.item + b.item
  := by
-- proof
  simp [Tensor.item, HAdd.hAdd]
  change (a.data.map (fun x => x + b.data[0])).get ⟨0, Nat.zero_lt_one⟩ =
    a.data.get ⟨0, Nat.zero_lt_one⟩ + b.data[0]
  erw [Vector.GetMap.eq.UFnGet.fin a.data (fun x => x + b.data[0]) ⟨0, Nat.zero_lt_one⟩]

private lemma item_div
-- given
  (a : Tensor ℝ* [])
  (c : ℝ*) :
-- imply
  (a / c).item = a.item / c
  := by
-- proof
  simp [Tensor.item, HDiv.hDiv]
  change (a.data.map (fun x => x / c)).get ⟨0, Nat.zero_lt_one⟩ =
    a.data.get ⟨0, Nat.zero_lt_one⟩ / c
  erw [Vector.GetMap.eq.UFnGet.fin a.data (fun x => x / c) ⟨0, Nat.zero_lt_one⟩]

private lemma dot_transpose_item
  {m n k : ℕ}
-- given
  (A : Matrix (Fin m) (Fin k) ℝ*)
  (B : Matrix (Fin n) (Fin k) ℝ*)
  (i : Fin m)
  (j : Fin n) :
-- imply
  (A.toTensor @ B.transpose.toTensor)[i, j].item = (A * B.transpose) i j
  := by
-- proof
  rw [dot_item A B.transpose i j, Matrix.mul_apply]

private lemma transpose_item
  {n k : ℕ}
-- given
  (B : Matrix (Fin n) (Fin k) ℝ*)
  (t : Fin k)
  (j : Fin n) :
-- imply
  ((B.toTensorᵀ.get ⟨t, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩).item = B j t
  := by
-- proof
  have ht := EqGetT.fin B.toTensor j t
  simp at ht
  erw [congrArg Tensor.item ht]
  erw [toTensor_get' B j t]
  exact item_coe (B j t)

private lemma transpose_get
  {n k : ℕ}
-- given
  (B : Matrix (Fin n) (Fin k) ℝ*)
  (t : Fin k)
  (j : Fin n) :
-- imply
  B.toTensorᵀ[t, j] = (B j t : Tensor ℝ* [])
  := by
-- proof
  change (B.toTensorᵀ.get ⟨t, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩ = _
  have ht := EqGetT.fin B.toTensor j t
  erw [ht]
  exact toTensor_get' B j t

private lemma dot_t_item
  {m n k : ℕ}
-- given
  (A : Matrix (Fin m) (Fin k) ℝ*)
  (B : Matrix (Fin n) (Fin k) ℝ*)
  (i : Fin m)
  (j : Fin n) :
-- imply
  (A.toTensor @ B.toTensorᵀ)[i, j].item = (A * B.transpose) i j
  := by
-- proof
  have hdot :
    (A.toTensor @ B.toTensorᵀ)[i, j] =
      ∑ t : Fin k,
        id (α := Tensor ℝ* []) (A.toTensor)[i][t] * id (α := Tensor ℝ* []) (B.toTensorᵀ)[t][j] :=
    GetDot.eq.Sum_MulGetS.fin A.toTensor B.toTensorᵀ i j
  have hitem := congrArg Tensor.item hdot
  rw [hitem, item_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro t _
  conv_lhs =>
    arg 1
    arg 1
    rw [toTensor_get A i t]
  conv_lhs =>
    arg 1
    arg 2
    rw [transpose_get B t j]
  erw [item_hmul]
  simp [id, Matrix.transpose_apply]
  erw [item_coe (B j t)]
  erw [item_coe (A i t)]

private lemma coe_get_item
  {m n : ℕ}
-- given
  (A : Matrix (Fin m) (Fin n) ℝ)
  (i : Fin m)
  (j : Fin n) :
-- imply
  ((((A.toTensor : Tensor ℝ* [m, n])).get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩).item
    = (A i j : ℝ*)
  := by
-- proof
  have hg := toTensor_get' A i j
  have hm := GetMap.eq.MapGet.fin A.toTensor Hyperreal.ofReal ⟨i, by simp [Tensor.length]⟩
  have hm2 := GetMap.eq.MapGet.fin (A.toTensor.get ⟨i, by simp [Tensor.length]⟩) Hyperreal.ofReal
    ⟨j, by simp [Tensor.length]⟩
  erw [hm, hm2, hg]
  simp [Tensor.item, Tensor.map, List.Vector.map, GetElem.getElem]
  change (([↑(A i j)] : List ℝ*)[0]'(by simp)) = ↑(A i j)
  simp

private lemma xeq_item
-- given
  (a b : Tensor ℝ* []) :
-- imply
  a ≈ b ↔ a.item ≈ b.item
  := by
-- proof
  rw [XEq.is.XEqDataS, Vector.XEq.is.All_XEqGetS.fin]
  constructor
  ·
    intro h
    simpa [Tensor.item, GetElem.getElem] using h ⟨0, Nat.zero_lt_one⟩
  ·
    intro h i
    have hi : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    subst hi
    simpa [Tensor.item, GetElem.getElem] using h

private lemma get2_add
  {m n : ℕ}
-- given
  (X Y : Tensor ℝ* [m, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (((X + Y).get i).get j).item = ((X.get i).get j).item + ((Y.get i).get j).item
  := by
-- proof
  have h1 := GetAdd.eq.AddGetS.fin X Y i
  have h2 := GetAdd.eq.AddGetS.fin (X.get i) (Y.get i) j
  erw [h1, h2]
  exact item_add ((X.get i).get j) ((Y.get i).get j)

private lemma get2_div
  {m n : ℕ}
-- given
  (X : Tensor ℝ* [m, n])
  (c : ℝ*)
  (i : Fin m)
  (j : Fin n) :
-- imply
  (((X / c).get i).get j).item = ((X.get i).get j).item / c
  := by
-- proof
  have h1 := GetDiv.eq.DivGet.scalar.fin X c i
  have h2 := GetDiv.eq.DivGet.scalar.fin (X.get i) c j
  erw [h1, h2, item_div]
  rfl

private lemma get2_mul
  {m n : ℕ}
-- given
  (X : Tensor ℝ* [m, n])
  (c : ℝ*)
  (i : Fin m)
  (j : Fin n) :
-- imply
  (((X * c).get i).get j).item = ((X.get i).get j).item * c
  := by
-- proof
  have h1 := GetMul.eq.MulGet.scalar.fin X c i
  have h2 := GetMul.eq.MulGet.scalar.fin (X.get i) c j
  erw [h1, h2]
  simp [Tensor.item, HMul.hMul]
  change (((X.get i).get j).data.map (fun x => x * c)).get ⟨0, Nat.zero_lt_one⟩ =
    ((X.get i).get j).data.get ⟨0, Nat.zero_lt_one⟩ * c
  erw [Vector.GetMap.eq.UFnGet.fin ((X.get i).get j).data (fun x => x * c) ⟨0, Nat.zero_lt_one⟩]

private lemma band_one_apply
  [AddMonoidWithOne α]
-- given
  (m n l u : ℕ)
  (i : Fin m)
  (j : Fin n) :
-- imply
  ((Matrix.of fun (_ : Fin m) (_ : Fin n) => (1 : α)).band_part l u) i j
    = ((decide ((j : ℤ) - (i : ℤ) ∈ Icc (-(l : ℤ)) (u : ℤ))).toNat : α)
  := by
-- proof
  simp [Matrix.band_part, Matrix.of_apply]
  if h1 : (i : ℤ) ≤ (j : ℤ) + l then
    if h2 : (j : ℤ) ≤ (u : ℤ) + i then
      simp [h1, h2]
    else
      simp [h1, h2]
  else
    simp [h1]

private lemma band_entry
  {k : ℕ}
-- given
  (l u : ℕ)
  (i j : Fin k) :
-- imply
  ((((1 : Tensor ℝ* [k, k]).band_part l u).get i).get j).item =
    ((Matrix.of fun (_ _ : Fin k) => (1 : ℝ*)).band_part l u) i j
  := by
-- proof
  rw [BandPart.eq.Stack_BoolIn_Icc, band_one_apply]
  erw [EqGetStack.fin (fun r : Fin k =>
    [c < k] (↑(decide ((c : ℤ) - (r : ℤ) ∈ Icc (-(l : ℤ)) (u : ℤ))).toNat : Tensor ℝ* [])) i]
  erw [EqGetStack.fin (fun c : Fin k =>
    (↑(decide ((c : ℤ) - (i : ℤ) ∈ Icc (-(l : ℤ)) (u : ℤ))).toNat : Tensor ℝ* [])) j]
  unfold Tensor.item
  change ([↑(decide ((j : ℤ) - (i : ℤ) ∈ Icc (-(l : ℤ)) (u : ℤ))).toNat] : List ℝ*)[0]'(by simp) = _
  simp

private lemma get2_neg
  {m n : ℕ}
-- given
  (X : Tensor ℝ* [m, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (((-X).get i).get j).item = -((X.get i).get j).item
  := by
-- proof
  have h1 := GetNeg.eq.NegGet.fin X i
  have h2 := GetNeg.eq.NegGet.fin (X.get i) j
  erw [h1, h2]
  exact ItemNeg.eq.NegItem ((X.get i).get j)

set_option maxHeartbeats 800000 in
private lemma get2_sub
  {m n : ℕ}
-- given
  (X Y : Tensor ℝ* [m, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (((X - Y).get i).get j).item = ((X.get i).get j).item - ((Y.get i).get j).item
  := by
-- proof
  have hs : X - Y = X + -Y := sub_eq_add_neg X Y
  rw [hs]
  have hadd := get2_add X (-Y) i j
  have hneg := get2_neg Y i j
  rw [hadd, hneg, sub_eq_add_neg]

private lemma one_item
  {m n : ℕ}
-- given
  (i : Fin m)
  (j : Fin n) :
-- imply
  (((1 : Tensor ℝ* [m, n]).get i).get j).item = 1
  := by
-- proof
  have h1 := EqGet1_1.fin (s := [m, n]) (α := ℝ*) ⟨i, by simp [Tensor.length]⟩
  have h2 := EqGet1_1.fin (s := [n]) (α := ℝ*) ⟨j, by simp [Tensor.length]⟩
  simp at h1 h2
  change (((1 : Tensor ℝ* [m, n]).get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩).item = 1
  rw [h1]
  erw [h2]
  exact EqItem1'1 (α := ℝ*)

private lemma stack_toTensor
  {m n : ℕ}
-- given
  (A : Matrix (Fin m) (Fin n) ℝ*) :
-- imply
  ([i < m] [j < n] (A i j : Tensor ℝ* [])) = A.toTensor
  := by
-- proof
  unfold Matrix.toTensor
  rfl

private lemma mask_item
  {k : ℕ}
-- given
  (l : ℕ)
  (i j : Fin k) :
-- imply
  (((((1 : Tensor ℝ* [k, k]).band_part (l - 1) 0 - 1) * ∞).get i).get j).item =
    (((Matrix.of fun (_ _ : Fin k) => (1 : ℝ*)).band_part (l - 1) 0) i j - 1) * ∞
  := by
-- proof
  have hmul := get2_mul ((1 : Tensor ℝ* [k, k]).band_part (l - 1) 0 - 1) ∞ i j
  rw [hmul]
  have hsub := get2_sub ((1 : Tensor ℝ* [k, k]).band_part (l - 1) 0) (1 : Tensor ℝ* [k, k]) i j
  rw [hsub]
  rw [band_entry (l - 1) 0 i j, one_item i j]

set_option maxHeartbeats 800000 in
private lemma score_item
  {k d : ℕ}
-- given
  (l : ℕ)
  (Qn Kn : Matrix (Fin k) (Fin d) ℝ*)
  (i j : Fin k) :
-- imply
  let QT : Tensor ℝ* [k, d] := [r < k] [a < d] Qn r a
  let KT : Tensor ℝ* [k, d] := [r < k] [a < d] Kn r a
  let dots : Tensor ℝ* [k, k] := QT @ KTᵀ
  let maskT : Tensor ℝ* [k, k] :=
    ((1 : Tensor ℝ* [k, k]).band_part (l - 1) 0 - 1) * ∞
  ((((dots / √(d : ℝ*) + maskT).get i).get j).item) =
    (Qn * Kn.transpose) i j / √(d : ℝ*) +
      (((Matrix.of fun (_ _ : Fin k) => (1 : ℝ*)).band_part (l - 1) 0) i j - 1) * ∞ := by
-- proof
  dsimp
  erw [get2_add]
  conv_lhs =>
    arg 1
    erw [get2_div]
  conv_lhs =>
    arg 1
    arg 1
    change (((Qn.toTensor @ Kn.toTensorᵀ).get i).get j).item
    change (Qn.toTensor @ Kn.toTensorᵀ)[i, j].item
    rw [dot_t_item Qn Kn i j]
  conv_lhs =>
    arg 2
    rw [mask_item l i j]

private lemma score_eq
  {k d : ℕ}
-- given
  (l : ℕ)
  (Q K : Matrix (Fin k) (Fin d) ℝ*) :
-- imply
  let QT : Tensor ℝ* [k, d] := [r < k] [a < d] Q r a
  let KT : Tensor ℝ* [k, d] := [r < k] [a < d] K r a
  let dots : Tensor ℝ* [k, k] := QT @ KTᵀ
  let maskT : Tensor ℝ* [k, k] :=
    ((1 : Tensor ℝ* [k, k]).band_part (l - 1) 0 - 1) * ∞
  let S : Matrix (Fin k) (Fin k) ℝ* :=
    Matrix.of fun i j =>
      (Q * K.transpose) i j / √(d : ℝ*) +
        (((Matrix.of fun (_ _ : Fin k) => (1 : ℝ*)).band_part (l - 1) 0) i j - 1) * ∞
  dots / √(d : ℝ*) + maskT = S.toTensor := by
-- proof
  dsimp
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  apply Eq.of.Item
  have hs := score_item l Q K i j
  dsimp at hs
  rw [hs]
  let S : Matrix (Fin k) (Fin k) ℝ* :=
    Matrix.of fun i j =>
      (Q * K.transpose) i j / √(d : ℝ*) +
        (((Matrix.of fun (_ _ : Fin k) => (1 : ℝ*)).band_part (l - 1) 0) i j - 1) * ∞
  change _ = (((S.toTensor).get i).get j).item
  erw [toTensor_get' S i j]
  erw [item_coe (S i j)]
  rfl

private lemma soft_eq
  {k : ℕ}
-- given
  (S : Matrix (Fin k) (Fin k) ℝ*) :
-- imply
  (S.toTensor).softmax 1 = (S.softmax 1).toTensor
  := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  apply Eq.of.Item
  have hm := mat_softmax_item S i j
  change (((S.toTensor.softmax 1).get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩).item = _
  rw [hm]
  erw [toTensor_get' (S.softmax 1) i j]
  exact item_coe ((S.softmax 1) i j)

private lemma prod_eq
  {k d : ℕ}
-- given
  (A : Matrix (Fin k) (Fin k) ℝ*)
  (V : Matrix (Fin k) (Fin d) ℝ*) :
-- imply
  A.toTensor @ V.toTensor = (A * V).toTensor
  := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  apply Eq.of.Item
  have hd := dot_item A V i j
  change (A.toTensor @ V.toTensor)[i, j].item = _
  rw [hd]
  erw [toTensor_get' (A * V) i j]
  erw [item_coe ((A * V) i j)]
  simp [Matrix.mul_apply]

private lemma attn_eq
  {k d : ℕ}
-- given
  (l : ℕ)
  (Q K V : Matrix (Fin k) (Fin d) ℝ*) :
-- imply
  let QT : Tensor ℝ* [k, d] := [r < k] [a < d] Q r a
  let KT : Tensor ℝ* [k, d] := [r < k] [a < d] K r a
  let dots : Tensor ℝ* [k, k] := QT @ KTᵀ
  let maskT : Tensor ℝ* [k, k] :=
    ((1 : Tensor ℝ* [k, k]).band_part (l - 1) 0 - 1) * ∞
  let S : Matrix (Fin k) (Fin k) ℝ* :=
    Matrix.of fun i j =>
      (Q * K.transpose) i j / √(d : ℝ*) +
        (((Matrix.of fun (_ _ : Fin k) => (1 : ℝ*)).band_part (l - 1) 0) i j - 1) * ∞
  ((dots / √(d : ℝ*) + maskT).softmax) @ V.toTensor = (S.softmax 1 * V).toTensor := by
-- proof
  have hs := score_eq l Q K
  dsimp at hs ⊢
  rw [hs, soft_eq, prod_eq]

private lemma coe_scalar
-- given
  (x : ℝ) :
-- imply
  ((x : Tensor ℝ []) : Tensor ℝ* []) = ((x : ℝ*) : Tensor ℝ* [])
  := by
-- proof
  rfl

private lemma coe_stack
  {k d : ℕ}
-- given
  (X : Fin k → Fin d → ℝ) :
-- imply
  (([i < k] [a < d] (X i a : Tensor ℝ []) : Tensor ℝ [k, d]) : Tensor ℝ* [k, d])
    = [i < k] [a < d] ((X i a : ℝ*) : Tensor ℝ* [])
  := by
-- proof
  show (([i < k] [a < d] (X i a : Tensor ℝ []))).map Hyperreal.ofReal = _
  rw [MapStack.eq.Stack_Map]
  apply Eq.of.All_EqGetS.fin
  intro i
  erw [EqGetStack.fin]
  rw [MapStack.eq.Stack_Map]
  apply Eq.of.All_EqGetS.fin
  intro a
  erw [EqGetStack.fin (fun b : Fin d => Tensor.map Hyperreal.ofReal (X i b : Tensor ℝ []))]
  erw [EqGetStack.fin (fun r : Fin k => [b < d] ((X r b : ℝ*) : Tensor ℝ* []))]
  erw [EqGetStack.fin (fun b : Fin d => ((X i b : ℝ*) : Tensor ℝ* []))]
  exact coe_scalar (X i a)

private lemma xeq_toTensor
  {k d : ℕ}
  {A : Matrix (Fin k) (Fin d) ℝ}
  {B : Matrix (Fin k) (Fin d) ℝ*}
-- given
  (h : (A : Matrix (Fin k) (Fin d) ℝ*) ≈ B) :
-- imply
  (A.toTensor : Tensor ℝ* [k, d]) ≈ B.toTensor
  := by
-- proof
  apply XEq.of.All_XEqGetS.fin
  intro i
  apply XEq.of.All_XEqGetS.fin
  intro j
  change
    (((A.toTensor : Tensor ℝ* [k, d]).get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩)
      ≈ (B.toTensor.get ⟨i, by simp [Tensor.length]⟩).get ⟨j, by simp [Tensor.length]⟩
  erw [xeq_item]
  have ha := coe_get_item A i j
  have hb := toTensor_get' B i j
  rw [ha]
  erw [hb]
  erw [item_coe (B i j)]
  simpa [Matrix.of_apply] using h i j

private lemma div_get_item
  {n : ℕ}
-- given
  (X : Tensor ℝ* [n])
  (c : ℝ*)
  (i : Fin n) :
-- imply
  ((X / c).get i).item = (X.get i).item / c
  := by
-- proof
  have h := GetDiv.eq.DivGet.scalar.fin X c i
  simp at h
  erw [h, item_div]

private lemma une_item
  {d m : ℕ}
-- given
  (A : Tensor ℝ* [d])
  (B : Tensor ℝ* [d, m])
  (j : Fin m) :
-- imply
  ((A @ B).get ⟨j, by simp [matmul_shape, Tensor.length]⟩).item =
    ∑ k : Fin d, (A.get k).item * ((B.get k).get j).item
  := by
-- proof
  have h := GetDot.eq.Sum_MulGetS.une.fin A B j
  simp at h
  erw [h, item_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  simp [id]
  erw [item_hmul]

private lemma castT_get
  {m n : ℕ}
-- given
  (X : Tensor ℝ* [m, n])
  (p : Fin n)
  (q : Fin m) :
-- imply
  (((cast (congrArg (Tensor ℝ*) (List.EqSwap_0'1 m n)) Xᵀ).get p).get q) =
    (X.get q).get p
  := by
-- proof
  have hT := EqGetT.fin X q p
  simp at hT
  have hc := GetCast.as.Get.of.Eq.GtLength_0.right.fin
    (h₀ := by simp) (h₁ := List.EqSwap_0'1 m n) (Xᵀ) p
  have hc' := Eq.of.SEq hc
  simp at hc'
  erw [hc']
  exact hT

private lemma cast_get_item
  {p n : ℕ}
-- given
  (h : [p] = [n])
  (X : Tensor ℝ* [p])
  (i : Fin n) :
-- imply
  ((cast (congrArg (Tensor ℝ*) h) X).get i).item =
    (X.get ⟨(i : ℕ), by
    cases h
    exact i.isLt⟩).item
  := by
-- proof
  have hc := GetCast.as.Get.of.Eq.GtLength_0.right.fin (h₀ := by simp) (h₁ := h) X i
  have hc' := Eq.of.SEq hc
  simp at hc'
  erw [hc']

private lemma softmax_of_vec
  {n : ℕ}
  {x : Fin n → ℝ*}
  {X : Tensor ℝ* [n]}
-- given
  (hX : X = [k < n] (x k : Tensor ℝ* []))
  (i : Fin n) :
-- imply
  (X.softmax.get i).item = Exp.exp (x i) / ∑ k : Fin n, Exp.exp (x k)
  := by
-- proof
  have hs : X.softmax = ([k < n] (x k : Tensor ℝ* [])).softmax := congrArg Tensor.softmax hX
  have hstack := stack_softmax_item x i
  erw [hs]
  simpa [Tensor.length] using hstack

@[path]
private lemma main
  [NeZero (l : ℕ)]
  {n d_z : ℕ}
  {Z : (k : ℕ) ⇀ Matrix (Fin k) (Fin d_z) ℝ}
  {Q K V : ℕ → Fin d_z → ℝ}
-- given
  (h : ∀ k,
    let Qn : Matrix (Fin k) (Fin d_z) ℝ* := Matrix.of fun i a => Q i a
    let Kn : Matrix (Fin k) (Fin d_z) ℝ* := Matrix.of fun i a => K i a
    let Vn : Matrix (Fin k) (Fin d_z) ℝ* := Matrix.of fun i a => V i a
    let S : Matrix (Fin k) (Fin k) ℝ* :=
      Matrix.of fun i j =>
        (Qn * Kn.transpose) i j / √(d_z : ℝ*) +
          (((Matrix.of fun (_ _ : Fin k) => (1 : ℝ*)).band_part (l - 1) 0) i j - 1) * ∞
    (Z k : Matrix (Fin k) (Fin d_z) ℝ*) ≈ S.softmax 1 * Vn) :
-- imply
  let start := n + 1 - l
  let w := ((⟨start, n, 1⟩ : Slice).length n)
  let score (t : Fin (w + 1)) : ℝ* :=
    (∑ a : Fin d_z,
        (Q n a : ℝ*) *
          if _ : (t : ℕ) < w then (K (start + (t : ℕ)) a : ℝ*) else (K n a : ℝ*)) /
      √(d_z : ℝ*)
  let sm : Matrix (Fin 1) (Fin (w + 1)) ℝ* := Matrix.of fun _ t => score t
  let row : Fin d_z → ℝ* := fun a =>
    ∑ t : Fin (w + 1),
      (sm.softmax 1) ⟨0, by decide⟩ t *
        if _ : (t : ℕ) < w then (V (start + (t : ℕ)) a : ℝ*) else (V n a : ℝ*)
  (Z (n + 1) : Matrix (Fin (n + 1)) (Fin d_z) ℝ*) ≈
    Fin.append (Z n : Matrix (Fin n) (Fin d_z) ℝ*) (fun (_ : Fin 1) => row) := by
-- proof
  let Qt : ℕ → Tensor ℝ [d_z] := fun t => [a < d_z] (Q t a)
  let Kt : ℕ → Tensor ℝ [d_z] := fun t => [a < d_z] (K t a)
  let Vt : ℕ → Tensor ℝ [d_z] := fun t => [a < d_z] (V t a)
  let Zt : (k : ℕ) → Tensor ℝ [k, d_z] := fun k => (Z k).toTensor
  have hT :
    ∀ k,
      let Qn : Tensor ℝ* [k, d_z] := ([i < k] Qt i : Tensor ℝ [k, d_z])
      let Kn : Tensor ℝ* [k, d_z] := ([i < k] Kt i : Tensor ℝ [k, d_z])
      let Vn : Tensor ℝ* [k, d_z] := ([i < k] Vt i : Tensor ℝ [k, d_z])
      let QK : Tensor ℝ* [k, k] := Qn @ Knᵀ
      (Zt k : Tensor ℝ* [k, d_z]) ≈
        (QK / √(d_z : ℝ*) + ((1 : Tensor ℝ* [k, k]).band_part (l - 1) 0 - 1) * ∞).softmax @ Vn := by
    intro k
    extract_lets Qn Kn Vn QK
    let Qm : Matrix (Fin k) (Fin d_z) ℝ* := Matrix.of fun i a => (Q (i : ℕ) a : ℝ*)
    let Km : Matrix (Fin k) (Fin d_z) ℝ* := Matrix.of fun i a => (K (i : ℕ) a : ℝ*)
    let Vm : Matrix (Fin k) (Fin d_z) ℝ* := Matrix.of fun i a => (V (i : ℕ) a : ℝ*)
    have hQn : Qn = Qm.toTensor := by
      dsimp [Qn, Qt]
      erw [coe_stack (fun (i : Fin k) (a : Fin d_z) => Q (i : ℕ) a)]
      exact (stack_toTensor Qm).symm
    have hKn : Kn = Km.toTensor := by
      dsimp [Kn, Kt]
      erw [coe_stack (fun (i : Fin k) (a : Fin d_z) => K (i : ℕ) a)]
      exact (stack_toTensor Km).symm
    have hVn : Vn = Vm.toTensor := by
      dsimp [Vn, Vt]
      erw [coe_stack (fun (i : Fin k) (a : Fin d_z) => V (i : ℕ) a)]
      exact (stack_toTensor Vm).symm
    have hk := h k
    dsimp at hk
    have hZ := xeq_toTensor (A := Z k) hk
    dsimp [QK]
    rw [hQn, hKn, hVn]
    let dotsS : Tensor ℝ* [k, k] :=
      ([r < k] [a < d_z] (Qm r a : Tensor ℝ* [])) @
        ([r < k] [a < d_z] (Km r a : Tensor ℝ* []))ᵀ
    have hdots : Qm.toTensor @ Km.toTensorᵀ = dotsS := by
      rfl
    conv_rhs =>
      arg 1
      arg 1
      arg 1
      arg 1
      erw [hdots]
    have hA := attn_eq (k := k) l Qm Km Vm
    extract_lets QT KT dots maskT S at hA
    dsimp [dots, QT, KT, maskT] at hA
    dsimp [dotsS]
    rwa [hA]
  have hconc :=
    GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T.kv_cache
      (n := n) (Z := Zt) (Q := Qt) (K := Kt) (V := Vt) hT
  extract_lets start w score sm row
  extract_lets KnT VnT Kw Vw KT kT rowT at hconc
  intro i a
  if hlt : (i : ℕ) < n then
    have hblock :
      Fin.append (Z n : Matrix (Fin n) (Fin d_z) ℝ*) (fun (_ : Fin 1) => row) i a =
        (Z n ⟨(i : ℕ), hlt⟩ a : ℝ*) := by
      have hidx : Fin.castAdd 1 ⟨(i : ℕ), hlt⟩ = i := by
        ext
        simp
      have hL := Fin.append_left
        (Z n : Matrix (Fin n) (Fin d_z) ℝ*) (fun (_ : Fin 1) => row) ⟨(i : ℕ), hlt⟩
      have hentry := congrFun (hidx ▸ hL) a
      erw [Matrix.of_apply] at hentry
      exact hentry
    rw [hblock]
    simp [Matrix.of_apply]
    have hrows := All_XEqGetS.of.XEq.fin hconc
    have hrow := hrows i
    have happ := GetAppend.eq.Get.of.Lt.fin hlt
      (Zt n : Tensor ℝ* [n, d_z]) ([_ < 1] rowT)
    erw [happ] at hrow
    have hcol := All_XEqGetS.of.XEq.fin hrow a
    erw [xeq_item] at hcol
    have hl := coe_get_item (Z (n + 1)) i a
    have hr := coe_get_item (Z n) ⟨(i : ℕ), hlt⟩ a
    rwa [← hl, ← hr]
  else
    have hblock :
      Fin.append (Z n : Matrix (Fin n) (Fin d_z) ℝ*) (fun (_ : Fin 1) => row) i a =
        row a := by
      refine congrFun ((?_ : Fin.natAdd n (0 : Fin 1) = i) ▸ Fin.append_right
        (Z n : Matrix (Fin n) (Fin d_z) ℝ*) (fun (_ : Fin 1) => row) (0 : Fin 1)) a
      ext
      simp [Fin.natAdd]
      have := hlt
      have := i.isLt
      omega
    rw [hblock]
    simp [Matrix.of_apply]
    have hrows := All_XEqGetS.of.XEq.fin hconc
    have hrow := hrows i
    have happ := GetAppend.eq.Get_Sub.of.GtAdd.Ge.fin
      (i := (i : ℕ)) (m := n) (n := 1)
      (by omega) (by have := i.isLt; omega)
      (Zt n : Tensor ℝ* [n, d_z]) ([_ < 1] rowT)
    simp at happ
    erw [happ] at hrow
    have hcol := All_XEqGetS.of.XEq.fin hrow a
    erw [xeq_item] at hcol
    have hl := coe_get_item (Z (n + 1)) i a
    have heq :
      (((Zt (n + 1) : Tensor ℝ* [n + 1, d_z]).get i).get a).item =
        ((((Z (n + 1)).toTensor : Tensor ℝ* [n + 1, d_z]).get ⟨i, by simpa [Tensor.length] using i.isLt⟩).get
          ⟨a, by simp [Tensor.length]⟩).item := by
      rfl
    rw [← hl, ← heq]
    apply hcol.trans
    erw [EqGetStack.fin (fun (_ : Fin 1) => rowT)]
    let scoreT :=
      ((Tensor.map Hyperreal.ofReal (Qt n)) @ (KT ++ kT) / √(d_z : ℝ*)).softmax
    let valT := Vw ++ [_ < 1] (Tensor.map Hyperreal.ofReal (Vt n))
    have hrowT : rowT = scoreT @ valT := by
      rfl
    have hdot := GetDot.eq.Sum_MulGetS.une.fin scoreT valT a
    simp at hdot
    erw [hrowT, hdot]
    erw [item_sum]
    have hsum :
      (∑ t, (id (α := Tensor ℝ* []) (scoreT.get t) *
        id (α := Tensor ℝ* []) ((valT.get t).get a)).item) = row a := by
      dsimp [row]
      apply Finset.sum_congr rfl
      intro t _
      simp [id]
      erw [item_hmul]
      have hs : (scoreT.get t).item = (sm.softmax 1) ⟨0, by decide⟩ t := by
        let qrow := Tensor.map Hyperreal.ofReal (Qt n)
        let keys := KT ++ kT
        let dots := qrow @ keys
        let pre := dots / √(d_z : ℝ*)
        have hlen : Kw.length = ((⟨(n + 1 - l : ℕ), n, 1⟩ : Slice).length n) := by
          simp [Tensor.length]
        have hw : Kw.length = w := by
          simpa [w, start] using hlen
        have hshape : matmul_shape [d_z] ([d_z] ++ [Kw.length + 1]) = [w + 1] := by
          simp [matmul_shape, hw]
        let dots' : Tensor ℝ* [w + 1] := cast (congrArg (Tensor ℝ*) hshape) dots
        have hdiv (j : Fin (w + 1)) :
          ((dots' / √(d_z : ℝ*)).get j).item = (dots'.get j).item / √(d_z : ℝ*) :=
          div_get_item dots' (√(d_z : ℝ*)) j
        have hq (b : Fin d_z) : (qrow.get b).item = (Q n b : ℝ*) := by
          dsimp [qrow, Qt]
          erw [GetMap.eq.MapGet.fin ([a < d_z] (Q n a : Tensor ℝ [])) Hyperreal.ofReal b]
          erw [EqGetStack.fin (fun a : Fin d_z => (Q n a : Tensor ℝ []))]
          erw [coe_scalar (Q n b)]
          exact item_coe (Q n b : ℝ*)
        have hkey (j : Fin (w + 1)) (b : Fin d_z) :
          ((keys.get b).get j).item =
            if (j : ℕ) < w then (K (start + (j : ℕ)) b : ℝ*) else (K n b : ℝ*) := by
          if hj : (j : ℕ) < w then
            simp [hj]
            have hjK : (j : ℕ) < Kw.length := by simpa [hw] using hj
            have happ := GetAppend.eq.Get.of.Lt.batch hjK KT kT b
            simp [GetElem.getElem] at happ
            erw [happ]
            dsimp [KT]
            have hT := castT_get Kw b ⟨(j : ℕ), hjK⟩
            erw [hT]
            have hslice := GetGetSlice.eq.Get_Add.of.GtSubMin.fin
              (X := KnT) (j := start) (n := n) (i := (j : ℕ))
              (by simp [w, start, List.LengthSlice.eq.SubMin] at hj; omega)
            simp at hslice
            erw [hslice]
            dsimp [KnT, Kt]
            erw [coe_stack (fun (i : Fin n) (c : Fin d_z) => K (i : ℕ) c)]
            erw [EqGetStack.fin (fun i : Fin n => [c < d_z] ((K (i : ℕ) c : ℝ*) : Tensor ℝ* []))]
            erw [EqGetStack.fin (fun c : Fin d_z => ((K ((start + (j : ℕ)) : ℕ) c : ℝ*) : Tensor ℝ* []))]
            exact item_coe (K (start + (j : ℕ)) b : ℝ*)
          else
            simp [hj]
            have hge : (j : ℕ) ≥ Kw.length := by simpa [hw] using (by omega : (j : ℕ) ≥ w)
            have hlt : Kw.length + 1 > (j : ℕ) := by
              have := j.isLt
              omega
            have happ := GetAppend.eq.Get_Sub.of.GtAdd.Ge.batch hge hlt KT kT b
            simp [GetElem.getElem] at happ
            erw [happ]
            dsimp [kT]
            have hq1 : (j : ℕ) - Kw.length < 1 := by
              have := j.isLt
              omega
            have hT := castT_get
              ([_ < 1] Tensor.map Hyperreal.ofReal (Kt n)) b ⟨(j : ℕ) - Kw.length, hq1⟩
            erw [hT]
            erw [EqGetStack.fin (fun (_ : Fin 1) => Tensor.map Hyperreal.ofReal (Kt n))]
            dsimp [Kt]
            erw [GetMap.eq.MapGet.fin ([c < d_z] (K n c : Tensor ℝ [])) Hyperreal.ofReal b]
            erw [EqGetStack.fin (fun c : Fin d_z => (K n c : Tensor ℝ []))]
            erw [coe_scalar (K n b)]
            exact item_coe (K n b : ℝ*)
        have hentry (j : Fin (w + 1)) :
          ((dots' / √(d_z : ℝ*)).get j).item = score j := by
          rw [hdiv j]
          erw [cast_get_item hshape dots j]
          have hu := une_item qrow keys j
          simp at hu
          dsimp [dots]
          erw [hu]
          dsimp [score]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro b _
          erw [hq b, hkey j b]
        have hpre : cast (congrArg (Tensor ℝ*) hshape) pre = dots' / √(d_z : ℝ*) := by
          dsimp [dots', pre]
          rfl
        have hvec : dots' / √(d_z : ℝ*) = [j < w + 1] (score j : Tensor ℝ* []) := by
          apply Eq.of.All_EqGetS.fin
          intro j
          apply Eq.of.Item
          change
            ((dots' / √(d_z : ℝ*)).get j).item =
              (([k < w + 1] (score k : Tensor ℝ* [])).get j).item
          rw [hentry j]
          erw [EqGetStack.fin (fun k : Fin (w + 1) => (score k : Tensor ℝ* []))]
          exact item_coe (score j)
        have hmat : (sm.softmax 1) ⟨0, by decide⟩ t =
            Exp.exp (score t) / ∑ k : Fin (w + 1), Exp.exp (score k) := by
          unfold Matrix.softmax
          dsimp
          erw [Matrix.of_apply]
          dsimp [sm]
          erw [Matrix.of_apply]
        have htry : (scoreT.get t).item = (pre.softmax.get t).item := by
          rfl
        have htry0 : (pre.softmax.get t).item = ((pre.softmax 0).get t).item := by
          rfl
        have htryc : ((pre.softmax 0).get t).item =
            (((cast (congrArg (Tensor ℝ*) hshape) pre).softmax).get t).item := by
          rfl
        rw [hmat]
        exact (htry.trans (htry0.trans htryc)).trans
          (softmax_of_vec (x := score) (X := cast (congrArg (Tensor ℝ*) hshape) pre)
            (by rwa [hpre]) t)
      if ht : (t : ℕ) < w then
        simp [ht]
        have hv : ((valT.get t).get a).item = (V (start + (t : ℕ)) a : ℝ*) := by
          have happ := GetAppend.eq.Get.of.Lt.fin ht
            Vw ([_ < 1] (Tensor.map Hyperreal.ofReal (Vt n)))
          simp at happ
          erw [happ]
          have hslice := GetGetSlice.eq.Get_Add.of.GtSubMin.fin
            (X := VnT) (j := start) (n := n) (i := (t : ℕ))
            (by simp [w, start, List.LengthSlice.eq.SubMin] at ht; omega)
          simp at hslice
          erw [hslice]
          dsimp [VnT, Vt]
          erw [coe_stack (fun (i : Fin n) (b : Fin d_z) => V (i : ℕ) b)]
          erw [EqGetStack.fin (fun i : Fin n => [b < d_z] ((V (i : ℕ) b : ℝ*) : Tensor ℝ* []))]
          erw [EqGetStack.fin (fun b : Fin d_z => ((V ((start + (t : ℕ)) : ℕ) b : ℝ*) : Tensor ℝ* []))]
          exact item_coe (V (start + (t : ℕ)) a : ℝ*)
        rw [hs]
        erw [hv]
        rfl
      else
        simp [ht]
        have hv : ((valT.get t).get a).item = (V n a : ℝ*) := by
          have ht1 : w + 1 > (t : ℕ) := by
            have := t.isLt
            simp [Tensor.length, scoreT] at this
            exact this
          have happ := GetAppend.eq.Get_Sub.of.GtAdd.Ge.fin
            (i := (t : ℕ)) (m := w) (n := 1)
            (by omega) ht1
            Vw ([_ < 1] (Tensor.map Hyperreal.ofReal (Vt n)))
          simp at happ
          erw [happ]
          erw [EqGetStack.fin (fun (_ : Fin 1) => Tensor.map Hyperreal.ofReal (Vt n))]
          dsimp [Vt]
          erw [GetMap.eq.MapGet.fin ([b < d_z] (V n b : Tensor ℝ [])) Hyperreal.ofReal a]
          erw [EqGetStack.fin (fun b : Fin d_z => (V n b : Tensor ℝ []))]
          erw [coe_scalar (V n a)]
          exact item_coe (V n a : ℝ*)
        rw [hs]
        erw [hv]
        rfl
    erw [hsum]


-- created on 2026-11-07
