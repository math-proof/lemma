import stdlib.List.Vector.Basic
import Lemma.Algebra.Zero.eq.Replicate
import Lemma.Vector.One.eq.Replicate
import Lemma.Algebra.Add.eq.Map2
import Lemma.Algebra.Mul.eq.Map2
import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Algebra.GetMul.eq.MulGetS
import Lemma.Algebra.GetAdd.eq.AddGetS
import Lemma.Vector.GetInv.eq.InvGet
import Lemma.Vector.NeReplicateS.of.Ne.Gt_0
import Lemma.Vector.EqGet1'1
open Algebra Vector

namespace List.Vector

instance [AddSemigroup α] : AddSemigroup (Vector α n) where
  add_assoc a b c := by
    repeat rw [Add.eq.Map2]
    ext i
    repeat rw [get_map₂]
    apply add_assoc

instance [AddZeroClass α]  : AddZeroClass (Vector α n) where
  zero_add a := by
    rw [Add.eq.Map2]
    ext i
    simp [Zero.eq.Replicate]
  add_zero a := by
    rw [Add.eq.Map2]
    ext i
    simp [Zero.eq.Replicate]

instance [MulZeroClass α] : MulZeroClass (Vector α n) where
  zero_mul a := by
    rw [Mul.eq.Map2]
    ext i
    simp [Zero.eq.Replicate]
  mul_zero a := by
    rw [Mul.eq.Map2]
    ext i
    simp [Zero.eq.Replicate]

instance [AddCommMagma α] : AddCommMagma (Vector α n) where
  add_comm a b := by
    repeat rw [Add.eq.Map2]
    ext i
    simp [Zero.eq.Replicate]
    apply add_comm

instance [AddMonoid α] : AddMonoid (Vector α n) where
  zero_add
  add_zero
  nsmul n v := v.map (fun x => n • x)
  nsmul_zero x := by
    ext i
    simp [Zero.eq.Replicate]
    apply AddMonoid.nsmul_zero
  nsmul_succ n x := by
    ext i
    simp [Add.eq.Map2]
    apply AddMonoid.nsmul_succ

instance [AddCommSemigroup α] : AddCommSemigroup (Vector α n) where
  add_comm

instance [AddCommMonoid α] : AddCommMonoid (Vector α n) where
  nsmul_zero := AddMonoid.nsmul_zero
  nsmul_succ := AddMonoid.nsmul_succ
  zero_add
  add_zero
  add_comm

instance [Mul α] [Add α] [LeftDistribClass α]: LeftDistribClass (Vector α n) where
  left_distrib a b c := by
    ext i
    repeat rw [GetAdd.eq.AddGetS.fin]
    repeat rw [GetMul.eq.MulGetS.fin]
    rw [GetAdd.eq.AddGetS.fin]
    apply left_distrib

instance [Mul α] [Add α] [RightDistribClass α]: RightDistribClass (Vector α n) where
  right_distrib a b c := by
    ext i
    repeat rw [GetAdd.eq.AddGetS.fin]
    repeat rw [GetMul.eq.MulGetS.fin]
    rw [GetAdd.eq.AddGetS.fin]
    apply right_distrib

instance [Distrib α] : Distrib (Vector α n) where
  left_distrib
  right_distrib

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Vector α n) where
  zero_mul
  mul_zero
  left_distrib
  right_distrib

instance [Semigroup α] : Semigroup (Vector α n) where
  mul_assoc a b c := by
    ext i
    repeat rw [GetMul.eq.MulGetS.fin]
    apply mul_assoc

instance [SemigroupWithZero α] : SemigroupWithZero (Vector α n) where
  zero_mul
  mul_zero

instance [NonUnitalSemiring α] : NonUnitalSemiring (Vector α n) where
  mul_assoc

instance [MulOneClass α] : MulOneClass (Vector α n) where
  one_mul a := by
    rw [Mul.eq.Map2]
    ext i
    simp [One.eq.Replicate]
  mul_one a := by
    rw [Mul.eq.Map2]
    ext i
    simp [One.eq.Replicate]

instance [MulZeroOneClass α] : MulZeroOneClass (Vector α n) where
  one_mul
  mul_one
  zero_mul
  mul_zero

instance [NatCast α] : NatCast (Vector α n) where
  natCast a := List.Vector.replicate n a

instance [AddMonoidWithOne α] : AddMonoidWithOne (Vector α n) where
  natCast := NatCast.natCast
  natCast_zero := by
    simp [NatCast.natCast]
    rfl
  natCast_succ a := by
    simp [NatCast.natCast]
    ext i
    rw [GetAdd.eq.AddGetS.fin]
    rw [EqGet1'1.fin]
    repeat rw [get_replicate]

instance [AddCommMonoidWithOne α] : AddCommMonoidWithOne (Vector α n) where
  add_comm

instance [NonAssocSemiring α] : NonAssocSemiring (Vector α n) where
  one_mul
  mul_one
  zero_mul
  mul_zero
  left_distrib
  right_distrib
  natCast_zero := AddMonoidWithOne.natCast_zero
  natCast_succ := AddMonoidWithOne.natCast_succ

instance [MonoidWithZero α] : MonoidWithZero (Vector α n) where
  one_mul
  mul_one
  zero_mul
  mul_zero

instance [Semiring α] : Semiring (Vector α n) where
  one_mul
  mul_one
  natCast_zero := AddMonoidWithOne.natCast_zero
  natCast_succ := AddMonoidWithOne.natCast_succ

instance [Monoid α] : Monoid (Vector α n) where
  one_mul
  mul_one

instance [DivInvMonoid α] : DivInvMonoid (Vector α n) where
  div_eq_mul_inv a b := by
    ext i
    rw [GetDiv.eq.DivGetS.fin]
    rw [GetMul.eq.MulGetS.fin]
    rw [GetInv.eq.InvGet.fin]
    rw [div_eq_mul_inv]

instance [NeZero n] [Nontrivial α] : Nontrivial (Vector α n) where
  exists_pair_ne := by
    let ⟨x, y, h_eq⟩ := Nontrivial.exists_pair_ne (α := α)
    use List.Vector.replicate n x, List.Vector.replicate n y
    apply NeReplicateS.of.Ne.Gt_0 (NeZero.pos n) h_eq

instance [NNRatCast α] : NNRatCast (Vector α n) where
  nnratCast q := List.Vector.replicate n (NNRatCast.nnratCast q)

end List.Vector
