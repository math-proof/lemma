import Mathlib
import Instance.MvFormalGroup_NegV2

set_option autoImplicit false

noncomputable section

universe u v

namespace CerednikDrinfeld

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_comp_subst_apply subst_X map_subst constantCoeff_X constantCoeff_subst_eq_zero)

variable (p : ℕ) [Fact p.Prime]


namespace SpecialFormal

variable {p}
variable {B : Type u} [CommRing B] {B' : Type v} [CommRing B']

abbrev Series (B : Type u) [CommRing B] : Type u := Fin 2 → MvPowerSeries (Fin 2) B


def Series.addVia (F : MvFormalGroup 2 B) (φ ψ : Series B) : Series B :=
  fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i)


def IsLawHom (F G : MvFormalGroup 2 B) (φ : Series B) : Prop :=
  (∀ i, constantCoeff (φ i) = 0) ∧
  ∀ i, subst F.toPowerSeries (φ i) =
    subst
      (Sum.elim
        (fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
        fun j => subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (φ j))
      (G.toPowerSeries i)

namespace IsLawHom

variable {F G H : MvFormalGroup 2 B} {φ ψ : Series B}


end IsLawHom


theorem Series.comp_assoc (χ ψ φ : Series B) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (hφ : ∀ i, constantCoeff (φ i) = 0) : (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := by
  funext i
  exact subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hψ)
    (hasSubst_of_constantCoeff_zero hφ) (χ i)

theorem Series.id_comp (φ : Series B) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    (Series.id B).comp φ = φ := by
  funext i
  exact subst_X (hasSubst_of_constantCoeff_zero hφ) i


end SpecialFormal

open SpecialFormal

structure FormalODModule (p : ℕ) [Fact p.Prime] (B : Type u) [CommRing B] where

  F : MvFormalGroup 2 B

  isComm : F.IsComm

  act : Zp2 p → Series B

  varpi : Series B

  isLawHom_act : ∀ a, IsLawHom F F (act a)

  isLawHom_varpi : IsLawHom F F varpi

  act_one : act 1 = Series.id B

  act_mul : ∀ a b, act (a * b) = (act a).comp (act b)

  act_add : ∀ a b, act (a + b) = Series.addVia F (act a) (act b)

  varpi_comp_varpi : varpi.comp varpi = act (p : Zp2 p)

  varpi_comp_act : ∀ a, varpi.comp (act a) = (act (WittVector.frobenius a)).comp varpi

namespace FormalODModule

attribute [instance] FormalODModule.isComm

variable {p}
variable {B : Type u} [CommRing B] {B' : Type v} [CommRing B']


abbrev Lie (_X : FormalODModule p B) : Type u := Fin 2 → B

def lieAct (X : FormalODModule p B) (a : Zp2 p) : X.Lie →ₗ[B] X.Lie :=
  Matrix.mulVecLin (MvFormalGroup.linearPart (X.act a))

def lieZero (j : Zp2 p →+* B) (X : FormalODModule p B) : Submodule B X.Lie :=
  ⨅ a : Zp2 p, LinearMap.ker (X.lieAct a - j a • LinearMap.id)

def lieOne (j : Zp2 p →+* B) (X : FormalODModule p B) : Submodule B X.Lie :=
  ⨅ a : Zp2 p, LinearMap.ker (X.lieAct a - j (WittVector.frobenius a) • LinearMap.id)

def IsSpecial (j : Zp2 p →+* B) (X : FormalODModule p B) : Prop :=
  IsCompl (X.lieZero j) (X.lieOne j) ∧
    Module.Invertible B ↥(X.lieZero j) ∧ Module.Invertible B ↥(X.lieOne j)

def IsODHom (X Y : FormalODModule p B) (φ : Series B) : Prop :=
  IsLawHom X.F Y.F φ ∧ (∀ a, φ.comp (X.act a) = (Y.act a).comp φ) ∧
    φ.comp X.varpi = Y.varpi.comp φ

structure Hom (X Y : FormalODModule p B) where

  toSeries : Series B

  isODHom : IsODHom X Y toSeries

namespace IsODHom

variable {X Y Z : FormalODModule p B} {φ ψ : Series B}

theorem constantCoeff (h : IsODHom X Y φ) (i : Fin 2) : constantCoeff (φ i) = 0 := h.1.1 i


end IsODHom

namespace Hom

variable {X Y Z : FormalODModule p B}


end Hom

abbrev KerAlgebra (φ : Series B) : Type u :=
  MvPowerSeries (Fin 2) B ⧸ Ideal.span (Set.range φ)

def HasKernelOfDegree (φ : Series B) (d : ℕ) : Prop :=
  Module.Finite B (KerAlgebra φ) ∧ Module.Projective B (KerAlgebra φ) ∧
    ∀ (κ : Type u) [Field κ] (f : B →+* κ), Module.finrank κ (KerAlgebra (φ.map f)) = d


def HasHeight (X : FormalODModule p B) (h : ℕ) : Prop :=
  HasKernelOfDegree (X.act (p : Zp2 p)) (p ^ h)

end FormalODModule

structure SpecialFormalODModule (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : Zp2 p →+* B)
    extends FormalODModule p B where

  isSpecial : toFormalODModule.IsSpecial j

  hasHeight : toFormalODModule.HasHeight 4

namespace SpecialFormal

abbrev pIdeal (B : Type u) [CommRing B] : Ideal B := Ideal.span {(p : B)}

variable {p}


structure Rigidified (p : ℕ) [Fact p.Prime] {O : Type v} [CommRing O]
    (Φ : FormalODModule p (O ⧸ pIdeal p O)) (B : Type u) [CommRing B] where

  X : FormalODModule p B

  n : ℕ

  ρ : Series (B ⧸ pIdeal p B)

namespace Rigidified

variable {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
variable {B B' B'' : Type u} [CommRing B] [CommRing B'] [CommRing B'']


end Rigidified

structure ModuliPackage (p : ℕ) [Fact p.Prime] (O : Type v) [CommRing O] : Type (max (u + 1) v) where

  obj : ∀ (B : Type u) [CommRing B] (_ψ : O →+* B), IsNilpotent (p : B) → Type u

  map : ∀ {B B' : Type u} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B'),
    f.comp ψ = ψ' → obj B ψ hB → obj B' ψ' hB'

  map_id : ∀ {B : Type u} [CommRing B] {ψ : O →+* B} (hB : IsNilpotent (p : B)) (x : obj B ψ hB),
    map hB hB (RingHom.id B) (RingHom.id_comp ψ) x = x

  map_comp : ∀ {B B' B'' : Type u} [CommRing B] [CommRing B'] [CommRing B'']
    {ψ : O →+* B} {ψ' : O →+* B'} {ψ'' : O →+* B''}
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (g : B' →+* B'') (f : B →+* B') (hf : f.comp ψ = ψ') (hg : g.comp ψ' = ψ'') (x : obj B ψ hB),
    map hB hB'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) x =
      map hB' hB'' g hg (map hB hB' f hf x)

namespace ModuliPackage

variable {O : Type v} [CommRing O]


end ModuliPackage

end SpecialFormal

end CerednikDrinfeld

end
