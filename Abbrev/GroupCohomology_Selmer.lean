import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Dual.Lemmas
import Structure.GroupCohomology_Selmer

set_option autoImplicit false

open CategoryTheory Module

universe u

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

end Representation

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

noncomputable abbrev twist (A : Rep k G) (χ : G →* kˣ) : Rep k G :=
  Rep.of (A.ρ.twist χ)

end Rep

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} [Fintype ι] {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)


end groupCohomology
