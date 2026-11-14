-- Carved from Lemma/Definitions/Def_Dieudonne_WittHomColimit.lean: instance decls only.
import Mathlib
import Lemma.LinearMap.DatumAndHonda
import Instance.Dieudonne_WittVectorHom
import Lemma.RingHom.WittVectorHom

set_option autoImplicit false

open Function

universe u v w

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {n m l : ℕ}
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

noncomputable def verschiebungIter (k : ℕ) : WittVector p R →+ WittVector p R where
  toFun x := (WittVector.verschiebung (p := p) (R := R))^[k] x
  map_zero' := iterate_map_zero _ _
  map_add' := iterate_map_add _ _

@[simp] theorem verschiebungIter_apply (k : ℕ) (x : WittVector p R) :
    verschiebungIter k x = (WittVector.verschiebung (p := p) (R := R))^[k] x := rfl

noncomputable def shiftLE (h : n ≤ m) :
    TruncatedWittVector p n R →+ TruncatedWittVector p m R :=
  AddMonoidHom.liftOfRightInverse (WittVector.truncate n).toAddMonoidHom TruncatedWittVector.out
    (fun x => TruncatedWittVector.truncateFun_out x)
    ⟨(WittVector.truncate m).toAddMonoidHom.comp (verschiebungIter (m - n)),
      fun x hx => by
        change (WittVector.truncate n) x = 0 at hx
        rw [← RingHom.mem_ker, WittVector.mem_ker_truncate] at hx
        change (WittVector.truncate m) ((WittVector.verschiebung (p := p) (R := R))^[m - n] x) = 0
        ext ⟨i, hi⟩
        simp only [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
        by_cases him : i < m - n
        · exact WittVector.iterate_verschiebung_coeff_eq_zero x him
        · obtain ⟨k, rfl⟩ : ∃ k, i = k + (m - n) := ⟨i - (m - n), by omega⟩
          rw [WittVector.iterate_verschiebung_coeff]
          exact hx k (by omega)⟩

@[simp] theorem shiftLE_truncate (h : n ≤ m) (x : WittVector p R) :
    shiftLE h (WittVector.truncate n x) =
      WittVector.truncate m ((WittVector.verschiebung (p := p) (R := R))^[m - n] x) :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _
    (fun x => TruncatedWittVector.truncateFun_out x) _ _

theorem coeff_shiftLE (h : n ≤ m) (x : TruncatedWittVector p n R) (i : Fin m) :
    (shiftLE h x).coeff i =
      if hi : m - n ≤ (i : ℕ) then x.coeff ⟨i - (m - n), by omega⟩ else 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shiftLE_truncate, WittVector.coeff_truncate]
  split_ifs with hi
  · rw [WittVector.coeff_truncate]
    have hk : (i : ℕ) = (i - (m - n)) + (m - n) := by omega
    conv_lhs => rw [hk]
    exact WittVector.iterate_verschiebung_coeff x (m - n) _
  · exact WittVector.iterate_verschiebung_coeff_eq_zero x (by omega)

theorem coeff_shiftLE_add (h : n ≤ m) (x : TruncatedWittVector p n R) (i : Fin n) :
    (shiftLE h x).coeff ⟨i + (m - n), by omega⟩ = x.coeff i := by
  rw [coeff_shiftLE, dif_pos (by simp)]
  congr 1
  ext
  simp

@[simp] theorem shiftLE_refl (x : TruncatedWittVector p n R) : shiftLE le_rfl x = x :=
  TruncatedWittVector.ext fun i => by
    rw [coeff_shiftLE, dif_pos (by simp)]
    congr 1
    exact Fin.ext (by simp)

theorem shiftLE_shiftLE (h₁ : n ≤ m) (h₂ : m ≤ l) (x : TruncatedWittVector p n R) :
    shiftLE h₂ (shiftLE h₁ x) = shiftLE (h₁.trans h₂) x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shiftLE_truncate, shiftLE_truncate, shiftLE_truncate, ← Function.iterate_add_apply]
  congr 2
  omega

theorem map_shiftLE (f : R →+* S) (h : n ≤ m) (x : TruncatedWittVector p n R) :
    map f (shiftLE h x) = shiftLE h (map f x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_map, coeff_shiftLE]
    split_ifs
    · rfl
    · exact map_zero f

end TruncWitt

section WittHom

variable {R : Type u} [CommRing R] {p : ℕ} [hp : Fact p.Prime] {n m l : ℕ}
variable {A : Type v} [CommRing A] [Bialgebra R A]

open TruncWitt

theorem shiftLE_mem_wittHom (h : n ≤ m) {x : TruncatedWittVector p n A}
    (hx : x ∈ wittHom R p n A) : TruncWitt.shiftLE h x ∈ wittHom R p m A := by
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_shiftLE, map_shiftLE, map_shiftLE, hx, map_add]

variable (R p A) in
noncomputable def wittHomShiftLE (h : n ≤ m) : wittHom R p n A →+ wittHom R p m A where
  toFun x := ⟨TruncWitt.shiftLE h x, shiftLE_mem_wittHom h x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp] theorem wittHomShiftLE_refl (x : wittHom R p n A) : wittHomShiftLE R p A le_rfl x = x :=
  Subtype.ext (shiftLE_refl _)

theorem wittHomShiftLE_shiftLE (h₁ : n ≤ m) (h₂ : m ≤ l) (x : wittHom R p n A) :
    wittHomShiftLE R p A h₂ (wittHomShiftLE R p A h₁ x) = wittHomShiftLE R p A (h₁.trans h₂) x :=
  Subtype.ext (shiftLE_shiftLE h₁ h₂ _)

theorem wittHomMap_shiftLE {B : Type w} [CommRing B] [Bialgebra R B] (φ : A →ₐc[R] B)
    (h : n ≤ m) (x : wittHom R p n A) :
    wittHomMap p m φ (wittHomShiftLE R p A h x) = wittHomShiftLE R p B h (wittHomMap p n φ x) :=
  Subtype.ext (map_shiftLE _ h _)

instance wittHomShiftLE_directedSystem :
    DirectedSystem (fun n => ↥(wittHom R p n A)) fun _ _ h => wittHomShiftLE R p A h where
  map_self _ x := wittHomShiftLE_refl x
  map_map _ _ _ h₁ h₂ x := wittHomShiftLE_shiftLE h₁ h₂ x

end WittHom

section Colimit

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
variable (A : Type v) [CommRing A] [Bialgebra R A]

def DieudonneModule : Type v :=
  AddCommGroup.DirectLimit (fun n => ↥(wittHom R p n A)) fun _ _ h => wittHomShiftLE R p A h

namespace DieudonneModule

noncomputable instance instAddCommGroup : AddCommGroup (DieudonneModule R p A) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.DirectLimit (fun n => ↥(wittHom R p n A)) fun _ _ h => wittHomShiftLE R p A h))

noncomputable instance instInhabited : Inhabited (DieudonneModule R p A) := ⟨0⟩

noncomputable def of (n : ℕ) : wittHom R p n A →+ DieudonneModule R p A :=
  AddCommGroup.DirectLimit.of (fun n => ↥(wittHom R p n A)) (fun _ _ h => wittHomShiftLE R p A h) n

variable {R p A}
variable {n m : ℕ}

@[simp] theorem of_shiftLE (h : n ≤ m) (x : wittHom R p n A) :
    of R p A m (wittHomShiftLE R p A h x) = of R p A n x :=
  AddCommGroup.DirectLimit.of_f _ _

section Map

variable {B : Type w} [CommRing B] [Bialgebra R B]

variable (R p) in

noncomputable def map (φ : A →ₐc[R] B) : DieudonneModule R p A →+ DieudonneModule R p B :=
  AddCommGroup.DirectLimit.lift
    (fun n => ↥(wittHom R p n A)) (fun _ _ h => wittHomShiftLE R p A h)
    (DieudonneModule R p B)
    (fun n => (of R p B n).comp (wittHomMap p n φ))
    fun _ _ h x => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, wittHomMap_shiftLE, of_shiftLE]

end Map

end DieudonneModule

end Colimit


end Deformation
