import Mathlib

import Instance.AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Morphisms.Separated

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite Limits

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

namespace Scheme.OrderedAffineCover

variable (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover)


end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {π : V ⟶ Spec (.of R)}

structure Hom (F G : OModulePresheaf π) where

  app : ∀ U : V.Opens, F.obj U →ₗ[R] G.obj U
  app_smul : ∀ (U : V.Opens) (a : Γ(V, U)) (x : F.obj U), app U (a • x) = a • app U x
  naturality : ∀ {U U' : V.Opens} (h : U ≤ U'), app U ∘ₗ F.res h = G.res h ∘ₗ app U'

structure SES (F₁ F₂ F₃ : OModulePresheaf π) where

  inc : Hom F₁ F₂

  proj : Hom F₂ F₃
  injective : ∀ U : V.Opens, Function.Injective (inc.app U)
  surjective : ∀ U : V.Opens, Function.Surjective (proj.app U)
  exact : ∀ U : V.Opens, LinearMap.range (inc.app U) = LinearMap.ker (proj.app U)

structure AffHom (F G : OModulePresheaf π) where

  app : ∀ U : V.affineOpens, F.obj U.1 →ₗ[R] G.obj U.1
  app_smul : ∀ (U : V.affineOpens) (a : Γ(V, U.1)) (x : F.obj U.1), app U (a • x) = a • app U x
  naturality : ∀ {U U' : V.affineOpens} (h : U.1 ≤ U'.1), app U ∘ₗ F.res h = G.res h ∘ₗ app U'

structure AffSES (F₁ F₂ F₃ : OModulePresheaf π) where

  inc : AffHom F₁ F₂

  proj : AffHom F₂ F₃
  injective : ∀ U : V.affineOpens, Function.Injective (inc.app U)
  surjective : ∀ U : V.affineOpens, Function.Surjective (proj.app U)
  exact : ∀ U : V.affineOpens, LinearMap.range (inc.app U) = LinearMap.ker (proj.app U)

namespace Hom

variable {F G H : OModulePresheaf π}


variable (F) in


end Hom

namespace AffHom

variable {F G H : OModulePresheaf π}


variable (F) in


end AffHom


section Cochains

variable [IsSeparated π] (K : V.OrderedAffineCover) {F G : OModulePresheaf π}


end Cochains

end OModulePresheaf

end AlgebraicGeometry

end
