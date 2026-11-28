module

public import Def.Data.Tensor.Defs.Part4
public import Def.Data.Tensor.Select
public import Def.Data.Tensor.Resize
public import Def.Data.Tensor.Shape
public import Def.Data.Tensor.Sum
public import Def.Data.Tensor.Mean
public import Def.Data.Tensor.Bmm
public import Def.Data.Tensor.Prod
public import Def.Data.Tensor.Reshape
public import Def.Data.Tensor.Unsqueeze
public import Def.Data.Tensor.Repeat
public import Notation.Data.Tensor.Permute
public import Def.Data.Tensor.Item
public import Def.Data.Tensor.HStack
public import Theorem.Bool.HEq.of.All_HEq
public import Theorem.Nat.Le_Sub_1.of.Lt
public import Theorem.Nat.LtAddS.is.Lt
public import Theorem.Nat.GtVal_0.of.Ne_0
public import Theorem.Nat.LtSubS_1.of.Lt.Ne_0
public import Theorem.Nat.Ge_1.of.Gt_0
public import Theorem.Nat.EqAddSub.of.Ge
public import Theorem.Nat.EqAddMulDiv
public import Theorem.Int.LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg
public import Theorem.List.MapEnumerate.eq.Cons_MapEnumerate.of.All_Eq
public import Theorem.List.HeadD.eq.Get_0.of.GtLength_0
public import Theorem.List.LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1
public import Theorem.List.GtLength_0.of.Cons.in.CartesianProduct
public import Theorem.List.EqCons_Tail.of.GtLength_0
public import Theorem.List.LengthTake.gt.Zero.of.LengthTake.gt.Zero
public import Theorem.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
public import Theorem.List.Sub_1.lt.LengthTail.of.In_Ioo0Length
public import Theorem.List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
public import Theorem.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
public import Theorem.List.GetEraseIdx.eq.Get.of.Gt.GtLength
public import Theorem.List.In_CartesianProduct.of.In_CartesianProductCons
public import Theorem.List.Lt.of.In_CartesianProductCons
public import Theorem.Tensor.Length.eq.Get_0.of.GtLength_0
public import Theorem.Tensor.GtLength_0.of.GtLength_0
public import Theorem.Tensor.Eq.is.EqDataS
public import Theorem.Tensor.DataAdd.eq.AddDataS
public import Theorem.Tensor.DataMul.eq.MulDataS
public import Theorem.Tensor.DataDiv.eq.DivDataS
public import Theorem.Tensor.DataNeg.eq.NegData
public import Theorem.Tensor.DataInv.eq.InvData
public import Theorem.Tensor.EqData0'0
public import Theorem.Tensor.Length.eq.Get_0.of.GtLength
public import Theorem.Tensor.EqLength
public import Theorem.Tensor.LengthMap.eq.Length
public import Theorem.Tensor.Eq.is.Item
public import Def.Data.Tensor.Tensor
public import Def.Data.Tensor.Tensor.Part2

@[expose] public section

open Bool Nat Int List Tensor


instance : GetElem (Tensor α s) ℕ (Tensor α s.tail) fun X i => i < X.length where
  getElem X i h := X.get ⟨i, h⟩

instance : GetElem (Tensor α s) ℤ (Tensor α s.tail) fun X i => i ∈ Ico (-X.length : ℤ) X.length where
  getElem X i h :=
    have := LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg h
    let i := Slice.Add_Mul_DivSub1Sign_2 X.length i
    X[i.toNat]

instance : GetElem (Tensor α s) (Tensor ℕ []) (Tensor α s.tail) fun X i => i.data[0] < X.length where
  getElem X i h := X[i.data[0]]

instance : GetElem (Tensor α s) (Tensor ℤ []) (Tensor α s.tail) fun X i => i.data[0] ∈ Ico (-X.length : ℤ) X.length where
  getElem X i _ := X[i.data[0]]

instance : GetElem (Tensor α s) (Tensor ℕ [n].tail) (Tensor α s.tail) fun X i => i.data[0] < X.length where
  getElem X i _ := X[i.data[0]]

instance : GetElem (Tensor α s) (Tensor ℤ [n].tail) (Tensor α s.tail) fun X i => i.data[0] ∈ Ico (-X.length : ℤ) X.length where
  getElem X i _ := X[i.data[0]]

instance : GetElem (Tensor α (m :: s)) (Tensor (Fin k) [n].tail) (Tensor α s) fun _ _ => k ≤ m where
  getElem X i h := X[i.data[0]]

instance [AddSemigroup α] : AddSemigroup (Tensor α s) where
  add_assoc a b c := by
    apply Eq.of.EqDataS
    simp [DataAdd.eq.AddDataS]
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

instance [NegZeroClass α] : NegZeroClass (Tensor α s) where
  neg_zero := by
    apply Eq.of.EqDataS
    rw [DataNeg.eq.NegData]
    simp [EqData0'0]

instance [AddCommMagma α] : AddCommMagma (Tensor α s) where
  add_comm X Y := by
    apply Eq.of.EqDataS
    simp [DataAdd.eq.AddDataS]
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
  nsmul := NSMul.nsmul
  nsmul_zero := AddMonoid.nsmul_zero
  nsmul_succ := AddMonoid.nsmul_succ

instance [Mul α] [Add α] [LeftDistribClass α]: LeftDistribClass (Tensor α n) where
  left_distrib A B C := by
    apply Eq.of.EqDataS
    simp [DataAdd.eq.AddDataS]
    simp [DataMul.eq.MulDataS]
    rw [DataAdd.eq.AddDataS]
    apply left_distrib

instance [Mul α] [Add α] [RightDistribClass α]: RightDistribClass (Tensor α n) where
  right_distrib A B C := by
    apply Eq.of.EqDataS
    simp [DataAdd.eq.AddDataS]
    simp [DataMul.eq.MulDataS]
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
    simp [DataMul.eq.MulDataS]
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
    simp only [HSMul.hSMul, SMul.smul]
    exact SubNegMonoid.zsmul_zero' x.data
  zsmul_succ' n x := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    simp only [HSMul.hSMul, SMul.smul]
    convert SubNegMonoid.zsmul_succ' n x.data using 1
  zsmul_neg' n x := by
    apply Eq.of.EqDataS
    rw [DataNeg.eq.NegData]
    simp only [HSMul.hSMul, SMul.smul]
    convert SubNegMonoid.zsmul_neg' n x.data using 1

instance [AddGroup α] : AddGroup (Tensor α s) where
  neg_add_cancel x := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    rw [DataNeg.eq.NegData]
    simp [EqData0'0]

instance [DivInvMonoid α] : DivInvMonoid (Tensor α s) where
  div_eq_mul_inv a b := by
    apply Eq.of.EqDataS
    rw [DataDiv.eq.DivDataS]
    rw [DataMul.eq.MulDataS]
    rw [DataInv.eq.InvData]
    rw [DivInvMonoid.div_eq_mul_inv]

instance [NeZero s.prod] [Nontrivial α] : Nontrivial (Tensor α s) where
  exists_pair_ne := by
    let ⟨a, b, h_eq⟩ := Nontrivial.exists_pair_ne (α := List.Vector α s.prod)
    use ⟨a⟩, ⟨b⟩
    simp_all

instance [CommMagma α] : CommMagma (Tensor α s) where
  mul_comm X Y := by
    apply Eq.of.EqDataS
    simp [DataMul.eq.MulDataS]
    apply mul_comm

instance [CommSemigroup α] : CommSemigroup (Tensor α s) where
  mul_assoc := mul_assoc
  mul_comm := mul_comm

instance [CommMonoid α] : CommMonoid (Tensor α s) where
  mul_comm := mul_comm

instance [CommSemiring α] : CommSemiring (Tensor α s) where
  mul_comm := mul_comm

instance [AddCommGroup α] : AddCommGroup (Tensor α s) where
  add_comm := add_comm

instance [AddGroupWithOne α] : AddGroupWithOne (Tensor α s) where

instance [Ring α] : Ring (Tensor α s) where

instance [CommRing α] : CommRing (Tensor α s) where

instance [Add α] [IsLeftCancelAdd α] : IsLeftCancelAdd (Tensor α s) where
  add_left_cancel a := by
    unfold IsAddLeftRegular Function.Injective
    intro a₁ a₂ h
    simp at h
    apply Eq.of.EqDataS
    have h := congrArg Tensor.data h
    simp [DataAdd.eq.AddDataS] at h
    assumption

instance [AddLeftCancelSemigroup α] : AddLeftCancelSemigroup (Tensor α s) where

instance [AddLeftCancelMonoid α] : AddLeftCancelMonoid (Tensor α s) where

instance [AddCancelCommMonoid α] : AddCancelCommMonoid (Tensor α s) where

/--
0-d tensors inherit a linear order from the underlying scalar type.
Note: this coexists with the pointwise `LE` instance on `Tensor`; absolute value
uses the `Max` from this `LinearOrder`.
-/
noncomputable instance [LinearOrder α] : LinearOrder (Tensor α []) :=
  LinearOrder.lift' Tensor.item (by apply Eq.of.Item)

/-- Transport `LinearOrder` along any shape with length 0 (i.e. `s = []`). -/
noncomputable instance (priority := low) [LinearOrder α] {s : List ℕ}
    [Fact (s.length = 0)] : LinearOrder (Tensor α s) :=
  List.eq_nil_of_length_eq_zero (Fact.out (p := s.length = 0)) ▸
    inferInstanceAs (LinearOrder (Tensor α []))

/-- Two-element lists have length 2. -/
instance {a b : ℕ} : Fact ([a, b].length = 2) := ⟨rfl⟩

/-- Batch shape of a square matrix determinant is empty. -/
instance {s : List ℕ} [Fact (s.length = 2)] :
    Fact ((s.take (s.length - 2)).length = 0) :=
  ⟨by simp [Fact.out (p := s.length = 2)]⟩

