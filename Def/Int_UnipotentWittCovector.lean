module
public import Mathlib
public import Def.LinearMap_DatumAndHonda
public import Def.RingHom_WittVectorHom
public import Def.Int_WittHomColimit
public import Def.Ideal_FontaineHodge
public import Instance.Dieudonne_UnipotentWittCovector
set_option autoImplicit false
open Function


public section

universe u v w u' v'

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {S : Type v} [CommRing S]

noncomputable def frobeniusAddHom {n : ℕ} (hS : (p : S) = 0) :
    TruncatedWittVector p n S →+ TruncatedWittVector p n S where
  toFun := frobeniusFun
  map_zero' := frobeniusFun_zero
  map_add' := frobeniusFun_add hS

end TruncWitt

def UnipotentWittCovector (p : ℕ) [Fact p.Prime] (S : Type v) [CommRing S] : Type v :=
  AddCommGroup.DirectLimit (fun n => TruncatedWittVector p n S) fun _ _ h => TruncWitt.shiftLE h

namespace UnipotentWittCovector

section Basic

variable (p : ℕ) [hp : Fact p.Prime] (S : Type v) [CommRing S]

noncomputable def of (n : ℕ) : TruncatedWittVector p n S →+ UnipotentWittCovector p S :=
  AddCommGroup.DirectLimit.of (fun n => TruncatedWittVector p n S) (fun _ _ h => TruncWitt.shiftLE h) n

variable {p S}
variable {n m : ℕ}

section Lift

variable {P : Type w} [AddCommGroup P]

variable (p S) in

noncomputable def lift (g : ∀ n, TruncatedWittVector p n S →+ P)
    (hg : ∀ (n : ℕ) (x : TruncatedWittVector p n S), g (n + 1) (TruncWitt.shift x) = g n x) :
    UnipotentWittCovector p S →+ P :=
  AddCommGroup.DirectLimit.lift (fun n => TruncatedWittVector p n S) (fun _ _ h => TruncWitt.shiftLE h)
    P g fun _ _ h x => compat_shiftLE g hg h x

end Lift

variable (p S) in

noncomputable def verschiebung : UnipotentWittCovector p S →+ UnipotentWittCovector p S :=
  lift p S (fun n => (of p S n).comp (TruncWitt.verschiebung (p := p) (n := n) (R := S))) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← TruncWitt.shiftLE_succ,
      TruncWitt.verschiebung_shiftLE, of_shiftLE]

section Map

variable {T : Type w} [CommRing T] {U : Type u'} [CommRing U]

variable (p) in

noncomputable def map (f : S →+* T) : UnipotentWittCovector p S →+ UnipotentWittCovector p T :=
  lift p S (fun n => (of p T n).comp (TruncWitt.map (p := p) (n := n) f).toAddMonoidHom) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, AddMonoidHom.coe_coe, TruncWitt.map_shift,
      of_shift]

end Map

end Basic

section Frobenius

noncomputable def frobenius (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (S : Type v) [CommRing S] [Algebra R S] : UnipotentWittCovector p S →+ UnipotentWittCovector p S :=
  lift p S (fun n => (of p S n).comp (TruncWitt.frobeniusAddHom (natCast_eq_zero_of_algebra R p S)))
    fun n x => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, TruncWitt.frobeniusAddHom_apply,
        TruncWitt.frobeniusAddHom_apply, TruncWitt.frobeniusFun_shift, of_shift]

variable (R : Type u) [CommRing R] {p : ℕ} [hp : Fact p.Prime] [CharP R p]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {n : ℕ}

variable (p S) in

noncomputable def dieudonneDatum : DieudonneDatum (p : ℤ) (UnipotentWittCovector p S) where
  F := (frobenius R p S).toIntLinearMap
  V := (verschiebung p S).toIntLinearMap
  fv := LinearMap.ext fun z => frobenius_verschiebung R z
  vf := LinearMap.ext fun z => verschiebung_frobenius R z

end Frobenius

section WKer

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ}
variable {ℛ : Type u} [CommRing ℛ] {A : Type v} [CommRing A]

noncomputable def wKer (π : ℛ →+* A) : AddSubgroup (UnipotentWittCovector p A) where
  carrier := {z | ∃ (n : ℕ) (x : TruncatedWittVector p n A),
    x ∈ TruncWitt.fontaineKer p n π ∧ of p A n x = z}
  zero_mem' := ⟨0, 0, zero_mem _, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨n, x, hx, rfl⟩ ⟨m, y, hy, rfl⟩
    refine ⟨max n m, TruncWitt.shiftLE (le_max_left n m) x + TruncWitt.shiftLE (le_max_right n m) y,
      add_mem (TruncWitt.shiftLE_mem_fontaineKer _ hx) (TruncWitt.shiftLE_mem_fontaineKer _ hy), ?_⟩
    rw [map_add, of_shiftLE, of_shiftLE]
  neg_mem' := by
    rintro _ ⟨n, x, hx, rfl⟩
    exact ⟨n, -x, neg_mem hx, map_neg _ _⟩

variable {p} {π : ℛ →+* A}

end WKer

end UnipotentWittCovector

namespace DieudonneModule

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
variable (A : Type v) [CommRing A] [Bialgebra R A]

noncomputable def toCovector : DieudonneModule R p A →+ UnipotentWittCovector p A :=
  lift R p A (fun n => (UnipotentWittCovector.of p A n).comp (wittHom R p n A).subtype) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddSubgroup.subtype_apply,
      AddSubgroup.subtype_apply, coe_wittHomShift, UnipotentWittCovector.of_shift]

variable {R p A}
variable {n : ℕ}

section Eval

variable {T : Type w} [CommRing T] [Algebra R T]

variable (R p) in

noncomputable def eval (f : A →ₐ[R] T) : DieudonneModule R p A →+ UnipotentWittCovector p T :=
  (UnipotentWittCovector.map p f.toRingHom).comp (toCovector R p A)

variable (R p A T) in

noncomputable def evalMonoidHom :
    WithConv (A →ₐ[R] T) →* Multiplicative (DieudonneModule R p A →+ UnipotentWittCovector p T) where
  toFun f := Multiplicative.ofAdd (eval R p f.ofConv)
  map_one' := by
    rw [← ofAdd_zero]
    exact congrArg _ (AddMonoidHom.ext fun z => eval_convOne z)
  map_mul' f g := by
    rw [← ofAdd_add]
    exact congrArg _ (AddMonoidHom.ext fun z => eval_convMul f g z)

end Eval

end DieudonneModule

namespace UnipotentWittCovector.Examples

variable (p : ℕ) [hp : Fact p.Prime] (S : Type v) [CommRing S]

noncomputable def one : UnipotentWittCovector p S :=
  of p S 1 (TruncatedWittVector.mk p fun _ : Fin 1 => (1 : S))

end UnipotentWittCovector.Examples

end Deformation
