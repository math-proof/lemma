import stdlib.List.Vector.Basic
import Lemma.Algebra.Zero.eq.Replicate
import Lemma.Algebra.Add.eq.Map2
import Lemma.Algebra.Mul.eq.Map2
import Lemma.Algebra.GetMul.eq.MulGetS
import Lemma.Algebra.GetAdd.eq.AddGetS
open Algebra

namespace List.Vector

instance [AddSemigroup α] : AddSemigroup (Vector α n) where
  add_assoc a b c := by
    repeat rw [Add.eq.Map2]
    ext i
    repeat rw [get_map₂]
    apply add_assoc

instance [AddZeroClass α]  : AddZeroClass (Vector α n) where
  zero_add := by
    intro a
    rw [Add.eq.Map2]
    ext i
    simp [Zero.eq.Replicate]
  add_zero := by
    intro a
    rw [Add.eq.Map2]
    ext i
    simp [Zero.eq.Replicate]

instance [MulZeroClass α] : MulZeroClass (Vector α n) where
  zero_mul := by
    intro a
    rw [Mul.eq.Map2]
    ext i
    simp [Zero.eq.Replicate]
  mul_zero := by
    intro a
    rw [Mul.eq.Map2]
    ext i
    simp [Zero.eq.Replicate]

instance [AddCommMagma α] : AddCommMagma (Vector α n) where
  add_comm := by
    intro a b
    repeat rw [Add.eq.Map2]
    ext i
    simp [Zero.eq.Replicate]
    apply add_comm

instance [AddMonoid α] : AddMonoid (Vector α n) where
  zero_add := AddZeroClass.zero_add
  add_zero := AddZeroClass.add_zero
  nsmul n v := v.map (fun x => n • x)
  nsmul_zero := by
    intro v
    ext i
    simp [Zero.eq.Replicate]
    apply AddMonoid.nsmul_zero
  nsmul_succ := by
    intro n v
    ext i
    simp [Add.eq.Map2]
    apply AddMonoid.nsmul_succ

instance [AddCommSemigroup α] : AddCommSemigroup (Vector α n) where
  add_comm := AddCommMagma.add_comm

instance [AddCommMonoid α] : AddCommMonoid (Vector α n) where
  zero_add := AddMonoid.zero_add
  add_zero := AddMonoid.add_zero
  add_comm := AddCommSemigroup.add_comm
  nsmul := AddMonoid.nsmul
  nsmul_zero := AddMonoid.nsmul_zero
  nsmul_succ := AddMonoid.nsmul_succ

instance [Mul α] [Add α] [LeftDistribClass α]: LeftDistribClass (Vector α n) where
  left_distrib := by
    intros
    ext i
    repeat rw [GetAdd.eq.AddGetS.fin]
    repeat rw [GetMul.eq.MulGetS.fin]
    rw [GetAdd.eq.AddGetS.fin]
    apply left_distrib

instance [Mul α] [Add α] [RightDistribClass α]: RightDistribClass (Vector α n) where
  right_distrib := by
    intros
    ext i
    repeat rw [GetAdd.eq.AddGetS.fin]
    repeat rw [GetMul.eq.MulGetS.fin]
    rw [GetAdd.eq.AddGetS.fin]
    apply right_distrib

instance [Distrib α] : Distrib (Vector α n) where
  left_distrib := LeftDistribClass.left_distrib
  right_distrib := RightDistribClass.right_distrib

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Vector α n) where
  zero_mul := MulZeroClass.zero_mul
  mul_zero := MulZeroClass.mul_zero
  left_distrib := Distrib.left_distrib
  right_distrib := Distrib.right_distrib

instance [Semigroup α] : Semigroup (Vector α n) where
  mul_assoc := by
    intros
    ext i
    repeat rw [GetMul.eq.MulGetS.fin]
    apply mul_assoc

instance [SemigroupWithZero α] : SemigroupWithZero (Vector α n) where
  mul_assoc := Semigroup.mul_assoc
  zero_mul := MulZeroClass.zero_mul
  mul_zero := MulZeroClass.mul_zero

instance [NonUnitalSemiring α] : NonUnitalSemiring (Vector α n) where
  mul_assoc := Semigroup.mul_assoc


end List.Vector
