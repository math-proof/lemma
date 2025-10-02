import sympy.tensor.Basic
import Lemma.Logic.HEq.of.All_HEq
import Lemma.Algebra.HeadD.eq.Get_0.of.GtLength_0
import Lemma.Algebra.LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1
import Lemma.Algebra.Le_Sub_1.of.Lt
import Lemma.Algebra.MapEnumerate.eq.Cons_MapEnumerate.of.All_Eq
import Lemma.Algebra.LtAddS.is.Lt
import Lemma.Algebra.LtVal
import Lemma.Set.GtLength_0.of.Cons.in.CartesianProduct
import Lemma.Algebra.Eq_Cons_Tail.of.GtLength_0
import Lemma.Set.In_CartesianProduct.of.In_CartesianProductCons
import Lemma.Set.Lt.of.In_CartesianProductCons
import Lemma.Algebra.LengthTake.gt.Zero.of.LengthTake.gt.Zero
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GtLength_0.of.GtLength_0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength
import Lemma.Set.LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg
open Tensor Algebra Set Logic

def Tensor.get (t : Tensor α s) (i : Fin t.length) : Tensor α s.tail :=
  have h_i := LtVal i
  have h_GtLength_0 := GtLength_0.of.GtLength_0 (t := t) (by linarith)
  have h_EqHeadD := HeadD.eq.Get_0.of.GtLength_0 h_GtLength_0 1
  have := Get_0.eq.Length.of.GtLength_0 h_GtLength_0 t
  t.toVector[i]

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
def Indexed (base : Tensor α s) (indices : List ℕ) (h : indices ∈ (s.take indices.length).cartesianProduct) : Tensor α (s.drop indices.length) :=
  match indices with
  | .nil =>
    base
  | index :: indices =>
    have h_Gt_0 := GtLength_0.of.Cons.in.CartesianProduct h
    have h_Gt_0 := LengthTake.gt.Zero.of.LengthTake.gt.Zero h_Gt_0
    have h_shape := Eq_Cons_Tail.of.GtLength_0 h_Gt_0
    have h_in : index :: indices ∈ (s[0] :: s.tail.take indices.length).cartesianProduct := by rwa [h_shape] at h
    have h := In_CartesianProduct.of.In_CartesianProductCons h_in
    have := Lt.of.In_CartesianProductCons h_in
    have h_eq := Length.eq.Get_0.of.GtLength_0 h_Gt_0 base
    cast (by simp) (Indexed (base.get ⟨index, by rwa [h_eq]⟩) indices h)

def Tensor.getSlice
  (t : Tensor α s)
  (slice : Slice) :
  Tensor α (slice.length t.length :: s.tail) :=
  let tensors := (List.Vector.indices slice t.length).map fun i =>
    t[i].data
  ⟨cast (by simp) tensors.flatten⟩

def Sliced
  (t : Tensor α s)
  (slices : List Slice)
  {h_shape : slices.length ≤ s.length} :
  Tensor α ((slices.enumerate.map fun ⟨i, slice⟩ => slice.length s[i]) ++ s.drop slices.length) :=
  match h_slice : slices with
  | .nil =>
    t
  | slice :: slices =>
    match h_slices : slices with
    | .nil =>
      have := Length.eq.Get_0.of.GtLength_0 (s := s) (by simpa [h_shape]) t
      have : (slice.length t.length :: s.tail).prod = (slice.length s[0] :: List.drop 1 s).prod := by
        simp_all
      (⟨cast (by rw [this]) (t.getSlice slice).data⟩ : Tensor α (slice.length s[0] :: s.drop 1))
    | slices'h :: slices't =>
      have h_shape : s.length ≥ (slice :: slices).length:= by
        simp_all
      have : s.length > slices.length := by
        simp_all
        linarith
      have : (s.drop 1).length ≥ slices.length:= by
        simp
        apply Le_Sub_1.of.Lt
        assumption
      let shape := slices.enumerate.map fun ⟨i, slice⟩ => slice.length (s.drop 1)[i]
      let s_rest := (s.drop 1).drop slices.length
      let indices :
        List.Vector (Fin s[0]) (slice.length s[0]) :=
        List.Vector.indices slice s[0]
      let tensors :
        List.Vector (List.Vector α (shape.prod * s_rest.prod)) (slice.length s[0]) :=
        indices.map fun i : Fin s[0] =>
          have : i < t.length := by
            simp_all [Length.eq.Get_0.of.GtLength (by assumption) t]
          let ti : Tensor α (s.drop 1) := ⟨t[i].data.val, by simp⟩
          have h_shape : slices.length ≤ (s.drop 1).length := LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1 (by simp_all) h_shape
          let sliced : Tensor α (shape ++ s_rest) := Sliced ti slices (h_shape := h_shape)
          have h_eq : (shape ++ s_rest).prod = shape.prod * s_rest.prod := by
            simp
          cast (by rw [h_eq]) sliced.data
      have h_cons : slice.length s[0] :: shape = (slice :: slices).enumerate.map (fun ⟨i, slice⟩ => slice.length s[i]) := by
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
        have := MapEnumerate.eq.Cons_MapEnumerate.of.All_Eq h_all slice
        simp [f] at this
        rw [this]
      have h_prod : slice.length s[0] * shape.prod = ((slice :: slices).enumerate.map (fun ⟨i, slice⟩ => slice.length s[i])).prod := by
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
              rw [Add.comm]
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
  zero_add := AddZeroClass.zero_add
  add_zero := AddZeroClass.add_zero
  nsmul n X := ⟨n • X.data⟩
  nsmul_zero X := by
    apply Eq.of.EqDataS
    apply AddMonoid.nsmul_zero
  nsmul_succ n X := by
    apply Eq.of.EqDataS
    apply AddMonoid.nsmul_succ

instance [AddCommSemigroup α] : AddCommSemigroup (Tensor α n) where
  add_comm := AddCommMagma.add_comm

instance [AddCommMonoid α] : AddCommMonoid (Tensor α s) where
  zero_add := AddMonoid.zero_add
  add_zero := AddMonoid.add_zero
  add_comm := AddCommMagma.add_comm
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
  left_distrib := LeftDistribClass.left_distrib
  right_distrib := RightDistribClass.right_distrib

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Tensor α s) where
  zero_mul := MulZeroClass.zero_mul
  mul_zero := MulZeroClass.mul_zero
  left_distrib := Distrib.left_distrib
  right_distrib := Distrib.right_distrib

instance [Semigroup α] : Semigroup (Tensor α s) where
  mul_assoc A B C := by
    apply Eq.of.EqDataS
    repeat rw [DataMul.eq.MulDataS]
    apply mul_assoc

instance [SemigroupWithZero α] : SemigroupWithZero (Tensor α s) where
  mul_assoc := Semigroup.mul_assoc
  zero_mul := MulZeroClass.zero_mul
  mul_zero := MulZeroClass.mul_zero

instance [NonUnitalSemiring α] : NonUnitalSemiring (Tensor α s) where
  mul_assoc := Semigroup.mul_assoc
