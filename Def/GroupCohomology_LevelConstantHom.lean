import Mathlib
import Lemma.GroupCohomology.ContinuousUnramifiedLevel

set_option autoImplicit false

namespace groupCohomology

universe u

variable {G : Type u} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (k : Type u) [CommRing k] (V : Type u) [AddCommGroup V] [Module k V]

def levelConstantHom : Submodule k (G → V) where
  carrier := {φ | (∀ g h : G, φ (g * h) = φ g + φ h) ∧ IsLevelConstantSr₁ r S φ}
  add_mem' := fun {φ ψ} hφ hψ =>
    ⟨fun g h => by simp only [Pi.add_apply, hφ.1 g h, hψ.1 g h]; abel, hφ.2.add hψ.2⟩
  zero_mem' := ⟨fun _ _ => by simp, isLevelConstantSr₁_const r S (0 : V)⟩
  smul_mem' := fun c φ hφ =>
    ⟨fun g h => by simp only [Pi.smul_apply, hφ.1 g h, smul_add], hφ.2.comp (c • ·)⟩


variable {k}

def eqLevelConstantHom (Sg : Subgroup G) (M : Rep k G) : Submodule k (↥Sg → M) where
  carrier := {φ | φ ∈ levelConstantHom (r.comp Sg.subtype) S k M ∧
    ∀ g : G, ∀ s t : ↥Sg, (g⁻¹ * s * g : G) = t → M.ρ g (φ t) = φ s}
  add_mem' := fun {φ ψ} hφ hψ =>
    ⟨add_mem hφ.1 hψ.1, fun g s t hst => by simp only [Pi.add_apply, map_add, hφ.2 g s t hst, hψ.2 g s t hst]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ _ _ => by simp⟩
  smul_mem' := fun c φ hφ =>
    ⟨Submodule.smul_mem _ c hφ.1, fun g s t hst => by simp only [Pi.smul_apply, map_smul, hφ.2 g s t hst]⟩

end groupCohomology
