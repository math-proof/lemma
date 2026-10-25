import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzApplications
open RiemannHurwitzFormula CanonicalSheafCurves RiemannHurwitzDegree RiemannHurwitzApplications


namespace RiemannHurwitzApplications

/--
[genus_bound_cover_pos_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_bound_cover_pos_genus
  {g_X g_Y n degR : ℤ}
-- given
  (hR : 0 ≤ degR)
  (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + degR)
  (_h_gY : g_Y ≥ 1) :
-- imply
  g_X ≥ n * g_Y - (n - 1) := by
-- proof
  linarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_bound_cover_pos_genus_alt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_bound_cover_pos_genus_alt
  {g_X g_Y n degR : ℤ}
-- given
  (hR : 0 ≤ degR)
  (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + degR) :
-- imply
  g_X ≥ n * (g_Y - 1) + 1 := by
-- proof
  linarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_bound_cover_gY_ge_1_CurveCover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_bound_cover_gY_ge_1_CurveCover
  {f : CurveCoverData}
-- given
  (_h_gY : f.target.g ≥ 1)
  (h_decomp : f.morphism.deg_KX = f.morphism.degree * f.morphism.deg_KY + f.morphism.deg_R) :
-- imply
  f.source.g ≥ f.morphism.degree * f.target.g - (f.morphism.degree - 1) := by
-- proof
  have hRH := riemann_hurwitz_genus_form f h_decomp
  have hR := f.morphism.h_deg_R_nonneg
  nlinarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_cover_ge_target_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_cover_ge_target_genus
  {g_X g_Y n degR : ℤ}
-- given
  (hR : 0 ≤ degR)
  (hn : n ≥ 1)
  (h_gY : g_Y ≥ 1)
  (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + degR) :
-- imply
  g_X ≥ g_Y := by
-- proof
  nlinarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_cover_strict_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_cover_strict_inequality
  {g_X g_Y n degR : ℤ}
-- given
  (hR : 0 ≤ degR)
  (hn : n ≥ 2)
  (h_gY : g_Y ≥ 2)
  (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + degR) :
-- imply
  g_X > g_Y := by
-- proof
  nlinarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_cover_strict_inequality_CurveCover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_cover_strict_inequality_CurveCover
  {f : CurveCoverData}
-- given
  (hn : f.morphism.degree ≥ 2)
  (h_gY : f.target.g ≥ 2)
  (h_decomp : f.morphism.deg_KX = f.morphism.degree * f.morphism.deg_KY + f.morphism.deg_R) :
-- imply
  f.source.g > f.target.g := by
-- proof
  have hRH := riemann_hurwitz_genus_form f h_decomp
  have hR := f.morphism.h_deg_R_nonneg
  nlinarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_etale_cover_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_etale_cover_exact
  {g_X g_Y n : ℤ}
-- given
  (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + 0) :
-- imply
  g_X = n * (g_Y - 1) + 1 := by
-- proof
  linarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[luroth_theorem_target_genus_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma luroth_theorem_target_genus_zero
  {g_Y n degR : ℤ}
-- given
  (hR : 0 ≤ degR)
  (hn : n ≥ 1)
  (hgY : g_Y ≥ 0)
  (h_RH : 2 * (0 : ℤ) - 2 = n * (2 * g_Y - 2) + degR) :
-- imply
  g_Y = 0 := by
-- proof
  simp only [mul_zero, zero_sub] at h_RH
  nlinarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[ramification_formula_genus_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma ramification_formula_genus_zero
  {n degR : ℤ}
-- given
  (h_RH : 2 * (0 : ℤ) - 2 = n * (2 * (0 : ℤ) - 2) + degR) :
-- imply
  degR = 2 * (n - 1) := by
-- proof
  simp only [mul_zero, zero_sub] at h_RH
  linarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[degree_one_unramified_genus_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma degree_one_unramified_genus_zero
  {degR : ℤ}
-- given
  (h_RH : 2 * (0 : ℤ) - 2 = (1 : ℤ) * (2 * (0 : ℤ) - 2) + degR) :
-- imply
  degR = 0 := by
-- proof
  simp only [mul_zero, zero_sub, one_mul] at h_RH
  linarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[luroth_target_genus_zero_CurveCover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma luroth_target_genus_zero_CurveCover
  {f : CurveCoverData}
-- given
  (h_gX : f.source.g = 0)
  (hn : f.morphism.degree ≥ 1)
  (hgY : f.target.g ≥ 0)
  (h_decomp : f.morphism.deg_KX = f.morphism.degree * f.morphism.deg_KY + f.morphism.deg_R) :
-- imply
  f.target.g = 0 := by
-- proof
  have hRH := riemann_hurwitz_genus_form f h_decomp
  have hR := f.morphism.h_deg_R_nonneg
  rw [h_gX] at hRH
  simp only [mul_zero, zero_sub] at hRH
  nlinarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[ramification_formula_CurveCover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma ramification_formula_CurveCover
  {f : CurveCoverData}
-- given
  (h_gX : f.source.g = 0)
  (h_gY : f.target.g = 0)
  (h_decomp : f.morphism.deg_KX = f.morphism.degree * f.morphism.deg_KY + f.morphism.deg_R) :
-- imply
  f.morphism.deg_R = 2 * (f.morphism.degree - 1) := by
-- proof
  have hRH := riemann_hurwitz_genus_form f h_decomp
  rw [h_gX, h_gY] at hRH
  simp only [mul_zero, zero_sub] at hRH
  linarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_formula_cover_of_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_formula_cover_of_P1
  {g_X n degR : ℤ}
-- given
  (h_RH : 2 * g_X - 2 = n * (2 * (0 : ℤ) - 2) + degR) :
-- imply
  2 * g_X = degR - 2 * n + 2 := by
-- proof
  simp only [mul_zero, zero_sub] at h_RH
  linarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_zero_implies_degK_neg2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_zero_implies_degK_neg2
  {C : SmoothCompleteCurve}
-- given
  (h : C.g = 0) :
-- imply
  C.degK = -2 := by
-- proof
  have := deg_canonical_eq_2g_sub_2 C
  linarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_zero_degK_eq_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_zero_degK_eq_P1
  {C : SmoothCompleteCurve}
-- given
  (h : C.g = 0) :
-- imply
  C.degK = (mkCurve 0).degK := by
-- proof
  rw [genus_zero_implies_degK_neg2 C h]
  simp [mkCurve]

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_zero_numerical_invariants](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_zero_numerical_invariants
  {C : SmoothCompleteCurve}
-- given
  (h : C.g = 0) :
-- imply
  C.g = (mkCurve 0).g ∧ C.degK = (mkCurve 0).degK := by
-- proof
  constructor
  · rw [h]; rfl
  · exact genus_zero_degK_eq_P1 C h

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_zero_unique_numerical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_zero_unique_numerical
  {C C' : SmoothCompleteCurve}
-- given
  (hC : C.g = 0)
  (hC' : C'.g = 0) :
-- imply
  C.g = C'.g ∧ C.degK = C'.degK := by
-- proof
  constructor
  · rw [hC, hC']
  · have h1 := deg_canonical_eq_2g_sub_2 C
    have h2 := deg_canonical_eq_2g_sub_2 C'
    linarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_zero_cover_data](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_zero_cover_data
  {f : CurveCoverData}
-- given
  (h_gX : f.source.g = 0)
  (hn : f.morphism.degree ≥ 1)
  (hgY : f.target.g ≥ 0)
  (h_decomp : f.morphism.deg_KX = f.morphism.degree * f.morphism.deg_KY + f.morphism.deg_R) :
-- imply
  f.target.g = 0 ∧ f.morphism.deg_R = 2 * (f.morphism.degree - 1) := by
-- proof
  have h1 := luroth_target_genus_zero_CurveCover f h_gX hn hgY h_decomp
  exact ⟨h1, ramification_formula_CurveCover f h_gX h1 h_decomp⟩

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_formula_target_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_formula_target_P1
  {g_X n degR : ℤ}
-- given
  (h_RH : 2 * g_X - 2 = n * (2 * 0 - 2) + degR) :
-- imply
  2 * g_X = degR - 2 * n + 2 := by
-- proof
  linarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_formula_target_elliptic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_formula_target_elliptic
  {g_X n degR : ℤ}
-- given
  (hR : 0 ≤ degR)
  (h_RH : 2 * g_X - 2 = n * (2 * 1 - 2) + degR) :
-- imply
  g_X ≥ 1 := by
-- proof
  linarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[etale_cover_elliptic_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma etale_cover_elliptic_genus
  {g_X n : ℤ}
-- given
  (h_RH : 2 * g_X - 2 = n * (2 * 1 - 2) + 0) :
-- imply
  g_X = 1 := by
-- proof
  linarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[genus_ge_2_for_cover_of_general_type](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma genus_ge_2_for_cover_of_general_type
  {g_X g_Y n degR : ℤ}
-- given
  (hR : 0 ≤ degR)
  (hn : n ≥ 1)
  (h_gY : g_Y ≥ 2)
  (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + degR) :
-- imply
  g_X ≥ 2 := by
-- proof
  nlinarith

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[normal_domain_element_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma normal_domain_element_criterion
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  {a b : R}
-- given
  (hR : NormalDomainLocalizationData R)
  (hb : b ≠ 0)
  (h_local : ∀ (p : Ideal R), p.IsPrime → p ≠ ⊥ → p.height ≤ (1 : ℕ∞) → ∃ (r s : R), s ∉ p ∧ a * s = b * r) :
-- imply
  ∃ (q : R), a = b * q :=
-- proof
  hR.intersection_property a b hb h_local

end RiemannHurwitzApplications

namespace RiemannHurwitzApplications

/--
[dedekind_normal_domain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean)
-/
@[path]
lemma dedekind_normal_domain
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R] :
-- imply
  IsIntegrallyClosed R :=
-- proof
  inferInstance

end RiemannHurwitzApplications


-- created on 2026-10-23
