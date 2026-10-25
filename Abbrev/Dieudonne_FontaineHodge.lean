import Mathlib
import Structure.Dieudonne_DatumAndHonda
import Instance.Dieudonne_WittVectorHom
import Instance.Dieudonne_WittHomColimit

set_option autoImplicit false

open Function

universe u v w u'

namespace Deformation

namespace WittGhost

variable {p : ℕ} [hp : Fact p.Prime] {ℛ : Type u} [CommRing ℛ]

end WittGhost

namespace TruncWitt

section FontaineKer

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
variable {ℛ : Type u} [CommRing ℛ] {A : Type v} [CommRing A] (π : ℛ →+* A)

end FontaineKer

end TruncWitt

section Hodge

variable (R : Type w) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
variable {ℛ : Type u} [CommRing ℛ] {A : Type v} [CommRing A] [Bialgebra R A] (π : ℛ →+* A)

open TruncWitt DieudonneModule

end Hodge

namespace SpecialFibre

open scoped TensorProduct
variable {𝓞 : Type u} [CommRing 𝓞] {k : Type v} [CommRing k] [Algebra 𝓞 k]
variable {ℛ : Type w} [CommRing ℛ] [Algebra 𝓞 ℛ]

variable (𝓞 k ℛ) in

noncomputable abbrev reduction : ℛ →+* k ⊗[𝓞] ℛ :=
  (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom

end SpecialFibre

end Deformation
