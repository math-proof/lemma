import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

namespace TwistedPairing

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [AddCommGroup S] [Module ℂ S]

variable {π : G →* Module.End ℂ V}

section Level

variable [TopologicalSpace G]

variable (π) in

def IsLevelDenseAction (H : S →ₗ[ℂ] Module.End ℂ V) : Prop :=
  ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
    ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ K, ∀ x : V, ℓ (π k x) = ℓ x) →
      ∀ x₀ : V, (∀ k ∈ K, π k x₀ = x₀) → ∃ φ : S, ∀ x : V, H φ x = ℓ x • x₀

end Level

end TwistedPairing
