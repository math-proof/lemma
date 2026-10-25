import Structure.AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Pi
import Instance.AlgebraicGeometry_OrderedAffineCoverCech

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

structure Scheme.OrderedAffineCover (V : Scheme.{u}) where

  ι : Type u
  [instFintype : Fintype ι]
  [instLinearOrder : LinearOrder ι]

  U : ι → V.Opens
  isAffineOpen : ∀ i, IsAffineOpen (U i)
  iSup_eq_top : ⨆ i, U i = ⊤

attribute [instance] Scheme.OrderedAffineCover.instFintype Scheme.OrderedAffineCover.instLinearOrder

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)


variable (V) in


end Scheme.OrderedAffineCover

namespace Scheme.TwoAffineOpenCover

variable {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)


end Scheme.TwoAffineOpenCover

structure OModulePresheaf {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) where

  obj : V.Opens → Type u
  [addCommGroup : ∀ U, AddCommGroup (obj U)]

  [module : ∀ U, Module R (obj U)]

  [moduleSections : ∀ U, Module Γ(V, U) (obj U)]

  [isScalarTower : ∀ U, letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    IsScalarTower R Γ(V, U) (obj U)]

  res : ∀ {U U' : V.Opens}, U ≤ U' → obj U' →ₗ[R] obj U

  res_smul : ∀ {U U' : V.Opens} (h : U ≤ U') (a : Γ(V, U')) (x : obj U'),
    res h (a • x) = (V.presheaf.map (homOfLE h).op).hom a • res h x

  res_refl : ∀ U, res (le_refl U) = LinearMap.id

  res_comp : ∀ {U U' U'' : V.Opens} (h : U ≤ U') (h' : U' ≤ U''), res (h.trans h') = res h ∘ₗ res h'

attribute [instance] OModulePresheaf.addCommGroup OModulePresheaf.module OModulePresheaf.moduleSections
  OModulePresheaf.isScalarTower

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)


variable (π) in


section TwoChart

variable (𝒱 : V.TwoAffineOpenCover)


end TwoChart

end OModulePresheaf

end AlgebraicGeometry

end
