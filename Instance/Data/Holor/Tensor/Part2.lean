import Def.Data.Holor.Defs.Part4
import Def.Data.Holor.Select
import Def.Data.Holor.Resize
import Def.Data.Holor.Shape
import Def.Data.Holor.Sum
import Def.Data.Holor.Mean
import Def.Data.Holor.Bmm
import Def.Data.Holor.Prod
import Def.Data.Holor.Reshape
import Def.Data.Holor.Unsqueeze
import Def.Data.Holor.Repeat
import Notation.Data.Holor.Permute
import Def.Data.Holor.Item
import Def.Data.Holor.HStack
import Lemma.Bool.HEq.of.All_HEq
import Lemma.Nat.Le_Sub_1.of.Lt
import Lemma.Nat.LtAddS.is.Lt
import Lemma.Nat.GtVal_0.of.Ne_0
import Lemma.Nat.LtSubS_1.of.Lt.Ne_0
import Lemma.Nat.Ge_1.of.Gt_0
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqAddMulDiv
import Lemma.Int.LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg
import Lemma.List.MapEnumerate.eq.Cons_MapEnumerate.of.All_Eq
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1
import Lemma.List.GtLength_0.of.Cons.in.CartesianProduct
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.LengthTake.gt.Zero.of.LengthTake.gt.Zero
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.List.Sub_1.lt.LengthTail.of.In_Ioo0Length
import Lemma.List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Lemma.List.In_CartesianProduct.of.In_CartesianProductCons
import Lemma.List.Lt.of.In_CartesianProductCons
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
import Lemma.Tensor.EqLength
import Lemma.Tensor.LengthMap.eq.Length
import Lemma.Tensor.Eq.is.Item
import Def.Data.Holor.Tensor.Part2
open Bool Nat Int List Tensor


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
  mul_comm := mul_comm

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
  add_left_cancel := IsLeftCancelAdd.add_left_cancel

instance [AddLeftCancelMonoid α] : AddLeftCancelMonoid (Tensor α s) where
  add_left_cancel := IsLeftCancelAdd.add_left_cancel

instance [AddCancelCommMonoid α] : AddCancelCommMonoid (Tensor α s) where
  add_left_cancel := IsLeftCancelAdd.add_left_cancel

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

