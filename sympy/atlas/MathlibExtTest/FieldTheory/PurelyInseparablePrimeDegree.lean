/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/FieldTheory/PurelyInseparablePrimeDegree.lean -/


import Lemma.Rat.PurelyInseparablePrimeDegree

set_option autoImplicit false

open IntermediateField Module Polynomial

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable (p : ℕ) [CharP K p] [IsPurelyInseparable K L]
variable [FiniteDimensional K L]

/-- Project the minimal-polynomial shape from the prime-degree classification. -/
example (hp : p.Prime) (hfin : finrank K L = p) :
    ∃ α : L, ∃ a : K, minpoly K α = X ^ p - C a := by
  obtain ⟨α, a, hmin, _, _⟩ :=
    IsPurelyInseparable.exists_minpoly_X_pow_sub_C_of_finrank_eq_prime
      K L p hp hfin
  exact ⟨α, a, hmin⟩

/-- Project the non-`p`th-power condition from the classification. -/
example (hp : p.Prime) (hfin : finrank K L = p) :
    ∃ a : K, ∀ b : K, b ^ p ≠ a := by
  obtain ⟨_, a, _, hpow, _⟩ :=
    IsPurelyInseparable.exists_minpoly_X_pow_sub_C_of_finrank_eq_prime
      K L p hp hfin
  exact ⟨a, hpow⟩

/-- Project generation of the whole extension from the classification. -/
example (hp : p.Prime) (hfin : finrank K L = p) :
    ∃ α : L, K⟮α⟯ = (⊤ : IntermediateField K L) := by
  obtain ⟨α, _, _, _, htop⟩ :=
    IsPurelyInseparable.exists_minpoly_X_pow_sub_C_of_finrank_eq_prime
      K L p hp hfin
  exact ⟨α, htop⟩
