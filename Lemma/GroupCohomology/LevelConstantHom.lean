import Mathlib
import Lemma.GroupCohomology.ContinuousUnramifiedLevel
import Def.GroupCohomology_LevelConstantHom

set_option autoImplicit false

namespace groupCohomology

universe u

variable {G : Type u} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (k : Type u) [CommRing k] (V : Type u) [AddCommGroup V] [Module k V]


variable {r S k V} in
theorem mem_levelConstantHom_iff (φ : G → V) :
    φ ∈ levelConstantHom r S k V ↔ (∀ g h : G, φ (g * h) = φ g + φ h) ∧ IsLevelConstantSr₁ r S φ := Iff.rfl

variable {k}


variable {r S} in
theorem mem_eqLevelConstantHom_iff (Sg : Subgroup G) (M : Rep k G) (φ : ↥Sg → M) :
    φ ∈ eqLevelConstantHom r S Sg M ↔ φ ∈ levelConstantHom (r.comp Sg.subtype) S k M ∧
      ∀ g : G, ∀ s t : ↥Sg, (g⁻¹ * s * g : G) = t → M.ρ g (φ t) = φ s := Iff.rfl

end groupCohomology
