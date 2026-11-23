module

public import Mathlib
public import Def.LinearMap_DatumAndHonda
public import Instance.Dieudonne_WittVectorHom
public import Abbrev.Dieudonne_WittVectorHom

@[expose] public section

set_option autoImplicit false

open Function

universe u v w

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]

noncomputable def map (f : R →+* S) : TruncatedWittVector p n R →+* TruncatedWittVector p n S :=
  RingHom.liftOfRightInverse (WittVector.truncate n) TruncatedWittVector.out
    TruncatedWittVector.truncateFun_out
    ⟨(WittVector.truncate n).comp (WittVector.map f), fun x hx => by
      rw [WittVector.mem_ker_truncate] at hx
      simp only [RingHom.mem_ker, RingHom.comp_apply, TruncatedWittVector.ext_iff,
        WittVector.coeff_truncate, WittVector.map_coeff, TruncatedWittVector.coeff_zero]
      exact fun i => by rw [hx i i.isLt]; exact map_zero f⟩

noncomputable def verschiebung : TruncatedWittVector p n R →+ TruncatedWittVector p n R :=
  AddMonoidHom.liftOfRightInverse (WittVector.truncate n).toAddMonoidHom TruncatedWittVector.out
    (fun x => TruncatedWittVector.truncateFun_out x)
    ⟨(WittVector.truncate n).toAddMonoidHom.comp WittVector.verschiebung, fun x hx => by
      change (WittVector.truncate n) x = 0 at hx
      rw [← RingHom.mem_ker, WittVector.mem_ker_truncate] at hx
      change (WittVector.truncate n) (WittVector.verschiebung x) = 0
      ext ⟨i, hi⟩
      simp only [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
      cases i with
      | zero => exact WittVector.verschiebung_coeff_zero x
      | succ j =>
        rw [WittVector.verschiebung_coeff_succ]
        exact hx j (Nat.lt_of_succ_lt hi)⟩

def frobeniusFun (x : TruncatedWittVector p n R) : TruncatedWittVector p n R :=
  TruncatedWittVector.mk p fun i => x.coeff i ^ p

omit hp in
noncomputable def shift : TruncatedWittVector p n R →+ TruncatedWittVector p (n + 1) R :=
  AddMonoidHom.liftOfRightInverse (WittVector.truncate n).toAddMonoidHom TruncatedWittVector.out
    (fun x => TruncatedWittVector.truncateFun_out x)
    ⟨(WittVector.truncate (n + 1)).toAddMonoidHom.comp WittVector.verschiebung, fun x hx => by
      change (WittVector.truncate n) x = 0 at hx
      rw [← RingHom.mem_ker, WittVector.mem_ker_truncate] at hx
      change (WittVector.truncate (n + 1)) (WittVector.verschiebung x) = 0
      ext ⟨i, hi⟩
      simp only [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
      cases i with
      | zero => exact WittVector.verschiebung_coeff_zero x
      | succ j =>
        rw [WittVector.verschiebung_coeff_succ]
        exact hx j (Nat.lt_of_succ_lt_succ hi)⟩

end TruncWitt

section WittHom

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
variable (A : Type v) [CommRing A] [Bialgebra R A]

open TruncWitt

noncomputable def wittHom : AddSubgroup (TruncatedWittVector p n A) where
  carrier := {x | map (comulRingHom R A) x =
    map (Algebra.TensorProduct.includeLeft : A →ₐ[R] TensorProduct R A A).toRingHom x +
    map (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R A A).toRingHom x}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
    rw [hx, hy]; abel
  neg_mem' {x} hx := by
    simp only [Set.mem_setOf_eq, map_neg] at hx ⊢
    rw [hx]; abel

variable {R p n A}

section Map

variable {B : Type w} [CommRing B] [Bialgebra R B]

variable (p n) in

noncomputable def wittHomMap (φ : A →ₐc[R] B) : wittHom R p n A →+ wittHom R p n B where
  toFun x := ⟨map (φ : A →ₐ[R] B).toRingHom x, map_mem_wittHom φ x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

end Map

variable (R p n A) in

noncomputable def wittHomVerschiebung : wittHom R p n A →+ wittHom R p n A where
  toFun x := ⟨TruncWitt.verschiebung x, verschiebung_mem_wittHom x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

section CharP

variable [CharP R p]

omit hp in

variable (R p n A) in

noncomputable def wittHomFrobenius : wittHom R p n A →+ wittHom R p n A where
  toFun x := ⟨TruncWitt.frobeniusFun x, frobeniusFun_mem_wittHom x.2⟩
  map_zero' := Subtype.ext frobeniusFun_zero
  map_add' _ _ := Subtype.ext (frobeniusFun_add (natCast_eq_zero_of_algebra R p A) _ _)

variable (R p n A) in

noncomputable def wittHomDieudonneDatum : DieudonneDatum (p : ℤ) (wittHom R p n A) where
  F := (wittHomFrobenius R p n A).toIntLinearMap
  V := (wittHomVerschiebung R p n A).toIntLinearMap
  fv := LinearMap.ext fun x => wittHomFrobenius_verschiebung x
  vf := LinearMap.ext fun x => wittHomVerschiebung_frobenius x

end CharP

variable (R p n A) in

noncomputable def wittHomShift : wittHom R p n A →+ wittHom R p (n + 1) A where
  toFun x := ⟨TruncWitt.shift x, shift_mem_wittHom x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

variable (R p A) in

noncomputable def wittHomRestrict {m : ℕ} (hm : n ≤ m) : wittHom R p m A →+ wittHom R p n A where
  toFun x := ⟨TruncatedWittVector.truncate hm x, truncateLE_mem_wittHom hm x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

end WittHom

end Deformation

end
