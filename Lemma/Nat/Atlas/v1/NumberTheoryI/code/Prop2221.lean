import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.Prop2221
open NumberField RayClassField GlobalCFT CosetDensity Prop2221


namespace CosetDensity

/--
[coset_density_eq_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2221.lean)
-/
@[path]
lemma coset_density_eq_formula
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
  {n : ℕ}
  {I : FracIdealsCoprime K 𝔪}
-- given
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
  (hn : 𝒞.index = n)
  (hn_pos : 0 < n) :
-- imply
  dirichletDensityCoset K 𝔪 𝒞 h_cong I = (1 - (DirichletDensity.sumOrdersNonprincipal K 𝔪 𝒞 h_cong : ℚ)) / (n : ℚ) := by
-- proof
  rw [dirichletDensityCoset_eq_congruence]
  simp only [dirichletDensityCongruence, DirichletDensity.sumOrdersNonprincipal, hn]

end CosetDensity

namespace CosetDensity

/--
[coset_density_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2221.lean)
-/
@[path]
lemma coset_density_nonneg
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
  {I : FracIdealsCoprime K 𝔪}
-- given
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
-- imply
  0 ≤ dirichletDensityCoset K 𝔪 𝒞 h_cong I := by
-- proof
  rw [dirichletDensityCoset_eq_congruence K 𝔪 𝒞 h_cong I]
  exact dirichletDensityCongruence_nonneg K 𝔪 𝒞 h_cong

end CosetDensity

namespace CosetDensity

/--
[proposition_22_21](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2221.lean)
-/
@[path]
lemma proposition_22_21
  {K : Type u}
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
  {n : ℕ}
  {I : FracIdealsCoprime K 𝔪}
-- given
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
  (hn : 𝒞.index = n)
  (hn_pos : 0 < n) :
-- imply
  (AllLValuesNonzero K 𝔪 𝒞 → dirichletDensityCoset K 𝔪 𝒞 h_cong I = 1 / (n : ℚ)) ∧ (¬ AllLValuesNonzero K 𝔪 𝒞 → dirichletDensityCoset K 𝔪 𝒞 h_cong I = 0) := by
-- proof
  set E := DirichletDensity.sumOrdersNonprincipal K 𝔪 𝒞 h_cong with hE_def
  have h_formula := coset_density_eq_formula K 𝔪 𝒞 h_cong n hn hn_pos I
  have h_nonneg := coset_density_nonneg K 𝔪 𝒞 h_cong I
  have h_equiv := DirichletDensity.allLValuesNonzero_iff_sumOrders_eq_zero K 𝔪 𝒞 h_cong
  have hn_pos_rat : (0 : ℚ) < (n : ℚ) := Nat.cast_pos.mpr hn_pos
  have hn_ne : (n : ℚ) ≠ 0 := ne_of_gt hn_pos_rat
  rw [h_formula] at h_nonneg
  have h_num_nonneg : 0 ≤ 1 - (E : ℚ) := by
    rwa [le_div_iff₀ hn_pos_rat, zero_mul] at h_nonneg
  have hE_le : E ≤ 1 := by
    have : (E : ℚ) ≤ 1 := by linarith
    exact_mod_cast this
  constructor
  ·
    intro h_all
    rw [h_equiv] at h_all
    rw [h_formula, h_all]
    simp
  ·
    intro h_not_all
    rw [h_equiv] at h_not_all
    have hE_eq : E = 1 := by omega
    rw [h_formula]
    rw [show DirichletDensity.sumOrdersNonprincipal K 𝔪 𝒞 h_cong = 1 from hE_eq]
    simp
end CosetDensity
namespace Prop2221
universe u in


namespace Prop2221

/--
[proposition_22_21](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2221.lean)
-/
@[path]
lemma proposition_22_21
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
  {n : ℕ}
  {I : FracIdealsCoprime K 𝔪}
-- given
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
  (hn : 𝒞.index = n)
  (hn_pos : 0 < n) :
-- imply
  (AllLValuesNonzero K 𝔪 𝒞 → dirichletDensityCoset K 𝔪 𝒞 h_cong I = 1 / (n : ℚ)) ∧ (¬ AllLValuesNonzero K 𝔪 𝒞 → dirichletDensityCoset K 𝔪 𝒞 h_cong I = 0) :=
-- proof
  CosetDensity.proposition_22_21 K 𝔪 𝒞 h_cong n hn hn_pos I

end Prop2221


-- created on 2026-10-23
