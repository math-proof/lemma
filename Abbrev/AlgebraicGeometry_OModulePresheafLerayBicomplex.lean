import Mathlib
import Instance.AlgebraicGeometry_OrderedAffineCoverCech
import Instance.AlgebraicGeometry_OrderedAffineCoverOf

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry.OModulePresheaf.Leray

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

section FiberAffine

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}

end FiberAffine

section LerayDC

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

abbrev HIdx (a : ℕ) := K.Idx a

abbrev VIdx (b : ℕ) := K'.Idx b

abbrev biOpen (a b : ℕ)
    (σ : HIdx K a) (τ : VIdx K' b) : V'.Opens :=
  K'.inter τ ⊓ (Opens.map p.base).obj (K.inter σ)

abbrev BiIdx (a b : ℕ) : Type u :=
  HIdx K a × VIdx K' b

abbrev biC (a b : ℕ) : Type u :=
  ∀ στ : BiIdx K K' a b,
    (OModulePresheaf.unit (p ≫ πZ)).obj (biOpen p K K' a b στ.1 στ.2)

end LerayDC

section RelAlt

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K' : Scheme.OrderedAffineCover V')

abbrev relAltC (U : Z.Opens) (b : ℕ) : Type u :=
  ∀ τ : K'.Idx b,
    (OModulePresheaf.unit (p ≫ πZ)).obj (K'.inter τ ⊓ (Opens.map p.base).obj U)

end RelAlt

section E2Iso

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

end E2Iso

end AlgebraicGeometry.OModulePresheaf.Leray

end
