import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
open Module FiniteDimensional SymplecticLinearAlgebra


namespace SymplecticLinearAlgebra

/--
[IsComplexStructure.apply_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CompatibleComplexStructures.lean)
-/
@[path]
lemma IsComplexStructure.apply_apply
  [AddCommGroup V]
  [Module ℝ V]
  {J : V →ₗ[ℝ] V}
  {v : V}
-- given
  (hJ : IsComplexStructure J) :
-- imply
  J (J v) = -v := by
-- proof
  have := LinearMap.ext_iff.mp hJ.sq_eq_neg v
  simp [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply] at this
  exact this

end SymplecticLinearAlgebra

namespace SymplecticLinearAlgebra

/--
[compatible_forms_convex_linear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CompatibleComplexStructures.lean)
-/
@[path]
lemma compatible_forms_convex_linear
  [AddCommGroup V]
  [Module ℝ V]
  {Ω₀ Ω₁ : LinearMap.BilinForm ℝ V}
  {J : V →ₗ[ℝ] V}
  {t : ℝ}
-- given
  (h₀ : IsCompatibleComplexStr Ω₀ J)
  (h₁ : IsCompatibleComplexStr Ω₁ J)
  (ht : t ∈ Set.Icc 0 1) :
-- imply
  IsCompatibleComplexStr ((1 - t) • Ω₀ + t • Ω₁) J := by
-- proof
  constructor
  · exact h₀.complex_str
  · intro u v
    simp [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [h₀.preserves u v, h₁.preserves u v]
  · intro u hu
    simp [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    have h0_pos := h₀.positive u hu
    have h1_pos := h₁.positive u hu
    obtain ⟨h_le0, h_le1⟩ := ht
    by_cases ht0 : t = 0
    · subst ht0; simp; linarith
    by_cases ht1 : t = 1
    · subst ht1; simp; linarith
    · have ht_pos : 0 < t := lt_of_le_of_ne h_le0 (Ne.symm ht0)
      have h1t_pos : 0 < 1 - t := by linarith [lt_of_le_of_ne h_le1 ht1]
      have term1 : 0 < (1 - t) * Ω₀ u (J u) := mul_pos h1t_pos h0_pos
      have term2 : 0 < t * Ω₁ u (J u) := mul_pos ht_pos h1_pos
      linarith

end SymplecticLinearAlgebra

/--
[exists_compatible_complex_structure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CompatibleComplexStructures.lean)
-/
@[path]
private lemma exists_compatible_complex_structure_eq
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω) :
-- imply
  ∃ J : V →ₗ[ℝ] V, IsCompatibleComplexStr Ω J := by
-- proof
  apply SymplecticLinearAlgebra.exists_compatible_complex_structure hΩ


-- created on 2026-10-23
