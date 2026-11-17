module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

set_option autoImplicit false

namespace RamificationChain

variable {G : Type*} [Group G]

noncomputable def wildSum (Gs : ℕ → Subgroup G) (cod : Subgroup G → ℕ) (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 N, Nat.card ↥(Gs i) * cod (Gs i)

noncomputable def wildDeltaChain (Gs : ℕ → Subgroup G) (cod : Subgroup G → ℕ) (N : ℕ) : ℕ :=
  wildSum Gs cod N / Nat.card ↥(Gs 0)

def HasseArfChain (Gs : ℕ → Subgroup G) : Prop :=
  ∀ i : ℕ, Gs i ≠ Gs (i + 1) →
    Nat.card ↥(Gs 0) ∣ ∑ j ∈ Finset.Icc 1 i, Nat.card ↥(Gs j)

end RamificationChain
