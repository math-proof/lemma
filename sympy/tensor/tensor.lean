import sympy.tensor.Basic
import Lemma.Bool.HEq.of.All_HEq
import Lemma.Nat.Le_Sub_1.of.Lt
import Lemma.Nat.LtAddS.is.Lt
import Lemma.Nat.GtVal_0.of.Ne_0
import Lemma.Nat.LtSubS_1.of.Lt.Ne_0
import Lemma.Nat.Ge_1.of.Gt_0
import Lemma.Nat.LtVal
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.List.MapEnumerate.eq.Cons_MapEnumerate.of.All_Eq
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1
import Lemma.List.GtLength_0.of.Cons.in.CartesianProduct
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.LengthTake.gt.Zero.of.LengthTake.gt.Zero
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.List.Sub_1.lt.LengthTail.of.In_Ioo0Length
import Lemma.List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.Lt_Length
import Lemma.List.In_CartesianProduct.of.In_CartesianProductCons
import Lemma.List.Lt.of.In_CartesianProductCons
import Lemma.Set.LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GtLength_0.of.GtLength_0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.DataInv.eq.InvData
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength
open Bool Set List Tensor Nat

def Tensor.get (X : Tensor α s) (i : Fin X.length) : Tensor α s.tail :=
  have h_i := LtVal i
  have h_GtLength_0 := GtLength_0.of.GtLength_0 (X := X) (by linarith)
  have h_EqHeadD := HeadD.eq.Get_0.of.GtLength_0 h_GtLength_0 1
  have := Get_0.eq.Length.of.GtLength_0 h_GtLength_0 X
  X.toVector[i]

/--
x[..., i] where ... means all indices before i
-/
def Tensor.getEllipsis (X : Tensor α s) (offset : Fin s.length) (i : Fin s[offset])  : Tensor α (s.eraseIdx offset) :=
  have h_s_length := Gt_0 offset
  if h : offset = ⟨0, h_s_length⟩ then
    cast
      (by
        substs h
        simp
      )
      (X.get ⟨i, by
        have h_i := LtVal i
        simp [h] at h_i
        rwa [Length.eq.Get_0.of.GtLength_0 h_s_length]
      ⟩)
  else
    have h := GtVal_0.of.Ne_0 h
    have h_lt := LtSubS_1.of.Lt.Ne_0 (by linarith) (by simp) (n := offset) (m := s.length)
    have h_1 := Ge_1.of.Gt_0 h
    have X : Tensor α (s.headD 1 :: s.tail.eraseIdx (offset - 1)) := Tensor.fromVector (
      X.toVector.map (
        ·.getEllipsis
          ⟨offset - 1, Sub_1.lt.LengthTail.of.In_Ioo0Length ⟨h, by simp⟩⟩
          ⟨i, by
            simp only [GetElem.getElem]
            rw [GetTail.eq.Get_Add_1.of.Lt_SubLength_1.fin]
            simp [EqAddSub.of.Ge h_1]
            assumption
          ⟩
      )
    )
    cast
      (by
        rw [EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1 (by assumption)]
        simp only [EqAddSub.of.Ge h_1]
        conv_rhs =>
          rw [Eq_Cons_Tail.of.GtLength_0 (v := s.eraseIdx offset) (show (s.eraseIdx offset).length > 0 by
            rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length]
            · linarith
            · simp
          )]
        congr
        rw [GetEraseIdx.eq.Get.of.Lt.Lt_Length]
        · apply List.HeadD.eq.Get_0.of.GtLength_0
        · simp
        · assumption
      )
      X

instance : GetElem (Tensor α s) ℕ (Tensor α s.tail) fun t i => i < t.length where
  getElem t i h := t.get ⟨i, h⟩

instance : GetElem (Tensor α s) ℤ (Tensor α s.tail) fun t i => i ∈ Ico (-t.length : ℤ) t.length where
  getElem t i h :=
    have := LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg h
    let i := Slice.Add_Mul_DivSub1Sign_2 t.length i
    t[i.toNat]

instance : GetElem (Tensor α s) (Tensor ℕ []) (Tensor α s.tail) fun t i => i.data[0] < t.length where
  getElem t i h := t[i.data[0]]

instance : GetElem (Tensor α s) (Tensor ℤ []) (Tensor α s.tail) fun t i => i.data[0] ∈ Ico (-t.length : ℤ) t.length where
  getElem t i _ := t[i.data[0]]

instance : GetElem (Tensor α s) (Tensor ℕ [n].tail) (Tensor α s.tail) fun t i => i.data[0] < t.length where
  getElem t i _ := t[i.data[0]]

instance : GetElem (Tensor α s) (Tensor ℤ [n].tail) (Tensor α s.tail) fun t i => i.data[0] ∈ Ico (-t.length : ℤ) t.length where
  getElem t i _ := t[i.data[0]]

instance : GetElem (Tensor α (m :: s)) (Tensor (Fin k) [n].tail) (Tensor α s) fun _ _ => k ≤ m where
  getElem t i h := t[i.data[0]]

/--
Represents a mathematical object with indices.
X[i, j, k].shape = X.shape.drop 3
-/
def Tensor.getElem (base : Tensor α s) (indices : List ℕ) (h : indices ∈ (s.take indices.length).cartesianProduct) : Tensor α (s.drop indices.length) :=
  match indices with
  | .nil =>
    base
  | index :: indices =>
    have h_Gt_0 := GtLength_0.of.Cons.in.CartesianProduct h
    have h_Gt_0 := LengthTake.gt.Zero.of.LengthTake.gt.Zero h_Gt_0
    have h_in : index :: indices ∈ (s[0] :: s.tail.take indices.length).cartesianProduct := by rwa [Eq_Cons_Tail.of.GtLength_0 h_Gt_0] at h
    have h := In_CartesianProduct.of.In_CartesianProductCons h_in
    have := Lt.of.In_CartesianProductCons h_in
    have h_eq := Length.eq.Get_0.of.GtLength_0 h_Gt_0 base
    cast (by simp) (getElem (base.get ⟨index, by rwa [h_eq]⟩) indices h)

def Tensor.getSlice
  (t : Tensor α s)
  (slice : Slice) :
  Tensor α (slice.length t.length :: s.tail) :=
  let tensors := (List.Vector.indices slice t.length).map fun i =>
    t[i].data
  ⟨cast (by simp) tensors.flatten⟩

def Tensor.getSlices
  (t : Tensor α s)
  (slices : List Slice)
  {h_shape : slices.length ≤ s.length} :
  Tensor α ((slices.enumerate.map fun ⟨i, index⟩ => index.length s[i]) ++ s.drop slices.length) :=
  match h_slice : slices with
  | .nil =>
    t
  | index :: slices =>
    match h_slices : slices with
    | .nil =>
      have := Length.eq.Get_0.of.GtLength_0 (s := s) (by simpa [h_shape]) t
      have : (index.length t.length :: s.tail).prod = (index.length s[0] :: List.drop 1 s).prod := by
        simp_all
      (⟨cast (by rw [this]) (t.getSlice index).data⟩ : Tensor α (index.length s[0] :: s.drop 1))
    | slices'h :: slices't =>
      have h_shape : s.length ≥ (index :: slices).length:= by
        simp_all
      have : s.length > slices.length := by
        simp_all
        linarith
      have : (s.drop 1).length ≥ slices.length:= by
        simp
        apply Le_Sub_1.of.Lt
        assumption
      let shape := slices.enumerate.map fun ⟨i, index⟩ => index.length (s.drop 1)[i]
      let s_rest := (s.drop 1).drop slices.length
      let indices :
        List.Vector (Fin s[0]) (index.length s[0]) :=
        List.Vector.indices index s[0]
      let tensors :
        List.Vector (List.Vector α (shape.prod * s_rest.prod)) (index.length s[0]) :=
        indices.map fun i : Fin s[0] =>
          have : i < t.length := by
            simp_all [Length.eq.Get_0.of.GtLength (by assumption) t]
          let ti : Tensor α (s.drop 1) := ⟨t[i].data.val, by simp⟩
          have h_shape : slices.length ≤ (s.drop 1).length := LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1 (by simp_all) h_shape
          let sliced : Tensor α (shape ++ s_rest) := getSlices ti slices (h_shape := h_shape)
          have h_eq : (shape ++ s_rest).prod = shape.prod * s_rest.prod := by
            simp
          cast (by rw [h_eq]) sliced.data
      have h_cons : index.length s[0] :: shape = (index :: slices).enumerate.map (fun ⟨i, index⟩ => index.length s[i]) := by
        simp [shape]
        let g := fun x : Fin slices.length × Slice => x.2.length s[x.1.val + 1]
        let f := fun x : Fin (slices.length + 1) × Slice => x.2.length s[x.1]
        have h_all : ∀ (i: Fin slices.length) (a : Slice), f ⟨
            ⟨i + 1, by
              apply LtAddS.of.Lt
              simp
            ⟩,
            a
          ⟩ = g ⟨i, a⟩ := by
          intro i a
          simp [f]
          simp [g]
        have := MapEnumerate.eq.Cons_MapEnumerate.of.All_Eq h_all index
        simp [f] at this
        rw [this]
      have h_prod : index.length s[0] * shape.prod = ((index :: slices).enumerate.map (fun ⟨i, index⟩ => index.length s[i])).prod := by
        rw [← h_cons]
        simp
      have h_length : slices.length = slices't.length + 1 := by
        rw [h_slices]
        simp_all
      ⟨
        cast (by
            simp [Mul_Mul.eq.MulMul]
            rw [h_prod]
            simp [← h_length]
            congr
            .
              apply HEq.of.All_HEq
              .
                intros
                congr <;>
                  simp_all
              .
                simp_all
            .
              simp [s_rest]
              rw [add_comm]
          )
          tensors.flatten
      ⟩

instance [AddSemigroup α] : AddSemigroup (Tensor α s) where
  add_assoc a b c := by
    apply Eq.of.EqDataS
    repeat rw [DataAdd.eq.AddDataS]
    apply add_assoc

instance [AddZeroClass α] : AddZeroClass (Tensor α s) where
  zero_add X := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    simp [EqData0'0]
  add_zero X := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    simp [EqData0'0]

instance [MulZeroClass α] : MulZeroClass (Tensor α s) where
  zero_mul X := by
    apply Eq.of.EqDataS
    rw [DataMul.eq.MulDataS]
    simp [EqData0'0]
  mul_zero X := by
    apply Eq.of.EqDataS
    rw [DataMul.eq.MulDataS]
    simp [EqData0'0]

instance [AddCommMagma α] : AddCommMagma (Tensor α s) where
  add_comm X Y := by
    apply Eq.of.EqDataS
    repeat rw [DataAdd.eq.AddDataS]
    apply add_comm

instance [AddMonoid α] : AddMonoid (Tensor α s) where
  zero_add
  add_zero
  nsmul n X := ⟨n • X.data⟩
  nsmul_zero X := by
    apply Eq.of.EqDataS
    apply AddMonoid.nsmul_zero
  nsmul_succ n X := by
    apply Eq.of.EqDataS
    apply AddMonoid.nsmul_succ

instance [AddCommSemigroup α] : AddCommSemigroup (Tensor α n) where
  add_comm

instance [AddCommMonoid α] : AddCommMonoid (Tensor α s) where
  zero_add
  add_zero
  add_comm
  nsmul := AddMonoid.nsmul
  nsmul_zero := AddMonoid.nsmul_zero
  nsmul_succ := AddMonoid.nsmul_succ

instance [Mul α] [Add α] [LeftDistribClass α]: LeftDistribClass (Tensor α n) where
  left_distrib A B C := by
    apply Eq.of.EqDataS
    repeat rw [DataAdd.eq.AddDataS]
    repeat rw [DataMul.eq.MulDataS]
    rw [DataAdd.eq.AddDataS]
    apply left_distrib

instance [Mul α] [Add α] [RightDistribClass α]: RightDistribClass (Tensor α n) where
  right_distrib A B C := by
    apply Eq.of.EqDataS
    repeat rw [DataAdd.eq.AddDataS]
    repeat rw [DataMul.eq.MulDataS]
    rw [DataAdd.eq.AddDataS]
    apply right_distrib

instance [Distrib α] : Distrib (Tensor α s) where
  left_distrib
  right_distrib

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Tensor α s) where
  zero_mul
  mul_zero
  left_distrib
  right_distrib

instance [Semigroup α] : Semigroup (Tensor α s) where
  mul_assoc A B C := by
    apply Eq.of.EqDataS
    repeat rw [DataMul.eq.MulDataS]
    apply mul_assoc

instance [SemigroupWithZero α] : SemigroupWithZero (Tensor α s) where
  mul_assoc
  zero_mul
  mul_zero

instance [NonUnitalSemiring α] : NonUnitalSemiring (Tensor α s) where
  mul_assoc

instance [MulOneClass α] : MulOneClass (Tensor α s) where
  one_mul a := by
    apply Eq.of.EqDataS
    rw [DataMul.eq.MulDataS]
    apply one_mul
  mul_one a := by
    apply Eq.of.EqDataS
    rw [DataMul.eq.MulDataS]
    apply mul_one

instance [MulZeroOneClass α] : MulZeroOneClass (Tensor α s) where
  one_mul
  mul_one
  zero_mul
  mul_zero

instance [NatCast α] : NatCast (Tensor α n) where
  natCast a := ⟨NatCast.natCast a⟩

instance [AddMonoidWithOne α] : AddMonoidWithOne (Tensor α s) where
  natCast_zero := by
    simp [NatCast.natCast]
    rfl
  natCast_succ a := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    apply AddMonoidWithOne.natCast_succ

instance [AddCommMonoidWithOne α] : AddCommMonoidWithOne (Tensor α s) where
  add_comm

instance [NonAssocSemiring α] : NonAssocSemiring (Tensor α s) where
  one_mul
  mul_one
  zero_mul
  mul_zero
  left_distrib
  right_distrib
  natCast_zero := AddMonoidWithOne.natCast_zero
  natCast_succ := AddMonoidWithOne.natCast_succ

instance [MonoidWithZero α] : MonoidWithZero (Tensor α s) where
  one_mul
  mul_one
  zero_mul
  mul_zero

instance [Semiring α] : Semiring (Tensor α s) where
  one_mul
  mul_one
  natCast_zero := AddMonoidWithOne.natCast_zero
  natCast_succ := AddMonoidWithOne.natCast_succ

instance [Monoid α] : Monoid (Tensor α s) where
  one_mul
  mul_one

instance [SubNegMonoid α] : SubNegMonoid (Tensor α s) where
  zsmul n v := ⟨n • v.data⟩
  zsmul_zero' x := by
    apply Eq.of.EqDataS
    simp
    rfl
  zsmul_succ' n x := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    simp
    have h := SubNegMonoid.zsmul_succ' n x.data
    simp at h
    assumption
  zsmul_neg' n x := by
    apply Eq.of.EqDataS
    rw [DataNeg.eq.NegData]
    simp
    have h := SubNegMonoid.zsmul_neg' n x.data
    simp at h
    rw [h]

instance [DivInvMonoid α] : DivInvMonoid (Tensor α s) where
  div_eq_mul_inv a b := by
    apply Eq.of.EqDataS
    rw [DataDiv.eq.DivDataS]
    rw [DataMul.eq.MulDataS]
    rw [DataInv.eq.InvData]
    rw [DivInvMonoid.div_eq_mul_inv]

instance [NNRatCast α] : NNRatCast (Tensor α s) where
  nnratCast q := ⟨NNRatCast.nnratCast q⟩

instance [NeZero s.prod] [Nontrivial α] : Nontrivial (Tensor α s) where
  exists_pair_ne := by
    let ⟨a, b, h_eq⟩ := Nontrivial.exists_pair_ne (α := List.Vector α s.prod)
    use ⟨a⟩, ⟨b⟩
    simp_all
