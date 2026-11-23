import Mathlib
import Def.FormalGroup_NegV2
import Def.FormalGroup_CartierModule
import Def.PowerSeries_CartierModuleHomothety
import Def.FormalGroup_CartierModuleWittAction
import Def.FormalGroup_CartierModuleIntVerschiebung
import Def.FormalGroup_CartierModuleBaseChange
import Def.CerednikDrinfeld_SpecialFormalModule
import Lemma.FormalGroup.CartierGradedPiece

set_option autoImplicit false

noncomputable section

universe u v w

namespace MvFormalGroup

open MvPowerSeries WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ}
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

namespace WittLaw

omit hp in

end WittLaw


end MvFormalGroup


namespace CerednikDrinfeld

namespace CartierLift

open MvPolynomial

variable (p : ℕ) (R : Type v) [CommRing R] {B : Type u}

def liftRel (u v : B) : MvPolynomial B R := X u * X v - C (p : R)

abbrev LiftRing (u v : B) : Type (max u v) := MvPolynomial B R ⧸ Ideal.span {liftRel p R u v}

variable {p R}

def liftVar (u v : B) (b : B) : LiftRing p R u v := Ideal.Quotient.mk _ (X b)

def liftHom [CommRing B] (j : R →+* B) (u v : B) (huv : u * v = p) : LiftRing p R u v →+* B :=
  Ideal.Quotient.lift _ (eval₂Hom j id) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, liftRel, map_sub, map_mul, eval₂Hom_X', eval₂Hom_X', eval₂Hom_C, map_natCast, id, id,
      huv, sub_self, mul_zero])

def liftConstants (a : ℕ → Fin 2 → B) (m : ℕ) (i : Fin 2) : LiftRing p R (a 0 0) (a 0 1) :=
  liftVar (a 0 0) (a 0 1) (a m i)

end CartierLift

namespace FormalODModule

open MvPowerSeries MvFormalGroup MvPowerSeries.CartierModule SpecialFormal PowerSeries MvPolynomial

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B] {B' : Type v} [CommRing B']

def IsHomogeneousVBasis (X : FormalODModule p B) (j : Zp2 p →+* B) (γ : Fin 2 → CartierModule p X.F) :
    Prop :=
  (∀ i : Fin 2, γ i ∈ X.gradedPiece j i) ∧ IsUnit (Matrix.of fun i k => tangent (γ i) k).det

def piIndex (m : ℕ) (i : Fin 2) : Fin 2 := ⟨(m + i + 1) % 2, Nat.mod_lt _ two_pos⟩

def HasStructureConstants (X : FormalODModule p B) (γ : Fin 2 → CartierModule p X.F)
    (a : ℕ → Fin 2 → B) : Prop :=
  ∀ (i : Fin 2) (N : ℕ), ∃ h : CartierModule p X.F,
    endAct X.varpiEnd (γ i) =
      (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := X.F)))^[m]
        (homothety (a m i) (γ (piIndex m i)))) +
        (⇑(verschiebungInt (p := p) (Φ := X.F)))^[N] h

end FormalODModule

end CerednikDrinfeld

end
