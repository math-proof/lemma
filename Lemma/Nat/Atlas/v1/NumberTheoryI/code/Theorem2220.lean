import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Theorem2220
open NumberField RayClassField GlobalCFT DirichletDensity


namespace DirichletDensity

/--
[allLValuesNonzero_iff_orders_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Theorem2220.lean)
-/
@[path]
lemma allLValuesNonzero_iff_orders_zero
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)} :
-- imply
  AllLValuesNonzero K 𝔪 𝒞 ↔ ∀ χ : PrimitiveCharsContaining K 𝔪 𝒞, ¬GlobalCFT.isPrincipalPrimitive K 𝔪 𝒞 χ → GlobalCFT.orderOfVanishingPrimitive K 𝔪 𝒞 χ = 0 :=
-- proof
  Iff.rfl

end DirichletDensity

namespace DirichletDensity

/--
[allLValuesNonzero_iff_sumOrders_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Theorem2220.lean)
-/
@[path]
lemma allLValuesNonzero_iff_sumOrders_eq_zero
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
-- given
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
-- imply
  AllLValuesNonzero K 𝔪 𝒞 ↔ sumOrdersNonprincipal K 𝔪 𝒞 h_cong = 0 := by
-- proof
  rw [allLValuesNonzero_iff_orders_zero]
  unfold sumOrdersNonprincipal
  simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies]
  constructor
  · intro h χ
    split_ifs with hp
    · rfl
    · exact h χ hp
  · intro h χ hχ
    have := h χ
    simp only [hχ, ↓reduceIte] at this
    exact this

end DirichletDensity

namespace DirichletDensity

/--
[dirichlet_density_congruence_subgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Theorem2220.lean)
-/
@[path]
lemma dirichlet_density_congruence_subgroup
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
  {n : ℕ}
-- given
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
  (hn : 𝒞.index = n)
  (hn_pos : 0 < n) :
-- imply
  (AllLValuesNonzero K 𝔪 𝒞 → dirichletDensityCongruence K 𝔪 𝒞 h_cong = 1 / (n : ℚ)) ∧ (¬ AllLValuesNonzero K 𝔪 𝒞 → dirichletDensityCongruence K 𝔪 𝒞 h_cong = 0) :=
-- proof
  GlobalCFT.theorem_22_20 K 𝔪 𝒞 h_cong n hn hn_pos

end DirichletDensity


-- created on 2026-10-23
