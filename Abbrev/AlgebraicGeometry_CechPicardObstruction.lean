import Mathlib
import Instance.AlgebraicGeometry_OrderedAffineCoverCech
import Abbrev.AlgebraicGeometry_OrderedAffineCoverComap
import Instance.AlgebraicGeometry_RelativePicardFunctor

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Scheme.Modules

variable {Y : Scheme.{u}}

abbrev CechTrivialisation (𝒱 : Y.OrderedAffineCover) (𝓜 : Y.Modules) : Type u :=
  ∀ a : 𝒱.ι, (Scheme.Modules.pullback (𝒱.U a).ι).obj 𝓜 ≅ SheafOfModules.unit ((𝒱.U a : Scheme.{u})).ringCatSheaf

namespace CechTrivialisation

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules}

end CechTrivialisation

end Scheme.Modules

namespace SmallExtension

open Scheme.TwoAffineOpenCover

variable {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
variable (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ιJ : V →ₗ[B₁] B₁)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
variable {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X)

end SmallExtension

end AlgebraicGeometry

end
