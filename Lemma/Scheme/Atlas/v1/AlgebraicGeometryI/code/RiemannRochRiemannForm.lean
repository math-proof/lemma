import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannRochRiemannForm
open CanonicalSheafCurves RiemannRochEulerCurves RiemannFormRR SheafCohCurvesFiniteness RiemannRochRiemannForm
open SheafCohCurvesFiniteness


namespace RiemannRochRiemannForm

/--
[riemann_form_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma riemann_form_general
  {C : SmoothCompleteCurve}
  {r d : ℤ}
  {SD : SerreDualityCurve C r d} :
-- imply
  SD.h0 - SD.h0_dual = d + r * (1 - C.g) := by
-- proof
  have hRR := chi_rr_curve C r d
  have hchi := SD.chi_decomp
  have hsd := SD.serre_dual
  linarith

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[riemann_form_general_alt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma riemann_form_general_alt
  {C : SmoothCompleteCurve}
  {r d : ℤ}
  {SD : SerreDualityCurve C r d} :
-- imply
  SD.h0 - SD.h0_dual = d - r * (C.g - 1) := by
-- proof
  have := riemann_form_general C r d SD
  linarith

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[riemann_form_line_bundle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma riemann_form_line_bundle
  {C : SmoothCompleteCurve}
  {d : ℤ}
  {SD : SerreDualityCurve C 1 d} :
-- imply
  SD.h0 - SD.h0_dual = d + 1 - C.g := by
-- proof
  have := riemann_form_general C 1 d SD
  linarith

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[riemann_inequality_line_bundle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma riemann_inequality_line_bundle
  {C : SmoothCompleteCurve}
  {d : ℤ}
  {SD : SerreDualityCurve C 1 d} :
-- imply
  SD.h0 ≥ d + 1 - C.g := by
-- proof
  have hform := riemann_form_line_bundle C d SD
  have h_dual_nn : SD.h0_dual ≥ 0 := by
    rwa [← SD.serre_dual]
  linarith

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[riemann_inequality_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma riemann_inequality_general
  {C : SmoothCompleteCurve}
  {r d : ℤ}
  {SD : SerreDualityCurve C r d} :
-- imply
  SD.h0 ≥ d + r * (1 - C.g) := by
-- proof
  have hform := riemann_form_general C r d SD
  have h_dual_nn : SD.h0_dual ≥ 0 := by
    rwa [← SD.serre_dual]
  linarith

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[riemann_roch_exact_when_h1_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma riemann_roch_exact_when_h1_zero
  {C : SmoothCompleteCurve}
  {r d : ℤ}
  {SD : SerreDualityCurve C r d}
-- given
  (h1_zero : SD.h1 = 0) :
-- imply
  SD.h0 = d + r * (1 - C.g) := by
-- proof
  have hRR := chi_rr_curve C r d
  have := SD.chi_decomp
  linarith

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[serre_duality_chi_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma serre_duality_chi_rank
  {C : SmoothCompleteCurve}
  {r d : ℤ} :
-- imply
  C.χ (r, d) + C.χ (r, r * C.degK - d) = 0 := by
-- proof
  rw [chi_rr_curve C r d, chi_rr_curve C r (r * C.degK - d)]
  have hK := deg_canonical_eq_2g_sub_2 C
  have : r * C.degK = r * (2 * C.g - 2) := by rw [hK]
  linarith [mul_sub r (2 * C.g) 2, mul_comm r (2 * C.g)]

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[serre_duality_chi_line_bundle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma serre_duality_chi_line_bundle
  {C : SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  C.χ (1, d) + C.χ (1, C.degK - d) = 0 :=
-- proof
  euler_char_dual_line_bundle C d

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[serreDualClass_line_bundle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma serreDualClass_line_bundle
  {C : SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  serreDualClass C 1 d = (1, C.degK - d) := by
-- proof
  simp [serreDualClass, one_mul]

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[serreDualClass_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma serreDualClass_degree
  {C : SmoothCompleteCurve}
  {r d : ℤ} :
-- imply
  (serreDualClass C r d).2 = r * (2 * C.g - 2) - d := by
-- proof
  simp only [serreDualClass]
  rw [deg_canonical_eq_2g_sub_2 C]

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[serre_duality_P1_verify](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma serre_duality_P1_verify
  {n : ℤ} :
-- imply
  (max (-n - 1) 0 : ℤ) = max ((-2 - n) + 1) 0 := by
-- proof
  congr 1; ring

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[riemann_roch_P1_max_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma riemann_roch_P1_max_identity
  {n : ℤ} :
-- imply
  (max (n + 1) 0 : ℤ) - max (-n - 1) 0 = n + 1 := by
-- proof
  by_cases hn : 0 ≤ n
  ·
    have h1 : (n + 1 : ℤ) ≥ 0 := by linarith
    have h2 : (-n - 1 : ℤ) ≤ 0 := by linarith
    rw [max_eq_left h1, max_eq_right h2]
    simp
  ·
    push Not at hn
    have h1 : (n + 1 : ℤ) ≤ 0 := by linarith
    have h2 : (-n - 1 : ℤ) ≥ 0 := by linarith
    rw [max_eq_right h1, max_eq_left h2]
    linarith

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[riemann_form_P1_verify](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma riemann_form_P1_verify
  {n : ℤ} :
-- imply
  (max (n + 1) 0 : ℤ) - max (-n - 1) 0 = n + 1 * (1 - 0) :=
-- proof
  riemann_roch_P1_max_identity n

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[riemann_inequality_P1_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma riemann_inequality_P1_nonneg
  {n : ℤ}
-- given
  (hn : n ≥ 0) :
-- imply
  (max (n + 1) 0 : ℤ) ≥ n + 1 := by
-- proof
  have : (n + 1 : ℤ) ≥ 0 := by linarith
  rw [max_eq_left this]

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[riemann_form_mkCurve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma riemann_form_mkCurve
  {g : ℕ}
  {r d : ℤ} :
-- imply
  (mkCurve g).χ (r, d) = d + r * (1 - (g : ℤ)) :=
-- proof
  mkCurve_euler_char g r d

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[serre_duality_mkCurve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma serre_duality_mkCurve
  {g : ℕ}
  {d : ℤ} :
-- imply
  (mkCurve g).χ (1, d) + (mkCurve g).χ (1, (mkCurve g).degK - d) = 0 :=
-- proof
  serre_duality_chi_line_bundle (mkCurve g) d

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[riemann_form_genus0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma riemann_form_genus0
  {d : ℤ} :
-- imply
  (mkCurve 0).χ (1, d) = d + 1 := by
-- proof
  rw [riemann_form_mkCurve]; ring

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[riemann_form_genus1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma riemann_form_genus1
  {d : ℤ} :
-- imply
  (mkCurve 1).χ (1, d) = d := by
-- proof
  rw [riemann_form_mkCurve]; ring

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[riemann_form_genus2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma riemann_form_genus2
  {d : ℤ} :
-- imply
  (mkCurve 2).χ (1, d) = d - 1 := by
-- proof
  rw [riemann_form_mkCurve]; ring

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[algebraic_abstract_consistency](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma algebraic_abstract_consistency
  [Field k]
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Algebra k A]
  [Module.Finite k A]
  {I : Ideal A}
  {g : ℤ}
-- given
  (hrr : SatisfiesRiemannRoch k A)
  (hI : I ≠ ⊥)
  (hg : g = (RiemannRochGeneral.arithmeticGenus k A : ℤ)) :
-- imply
  (lD k A I : ℤ) - (lKD k A I : ℤ) = (RiemannRochGeneral.lineBundleDegree k A I : ℤ) + 1 - g := by
-- proof
  have := hrr.rr_formula I hI
  rw [divisorEulerChar] at this
  linarith

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[corollary_30](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma corollary_30
  {C : SmoothCompleteCurve}
  {r d : ℤ}
  {SD : SerreDualityCurve C r d} :
-- imply
  SD.h0 - SD.h0_dual = d + r * (1 - C.g) ∧ SD.h0 ≥ d + r * (1 - C.g) :=
-- proof
⟨riemann_form_general C r d SD, riemann_inequality_general C r d SD⟩

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[corollary_30_line_bundle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma corollary_30_line_bundle
  {C : SmoothCompleteCurve}
  {d : ℤ}
  {SD : SerreDualityCurve C 1 d} :
-- imply
  SD.h0 - SD.h0_dual = d + 1 - C.g ∧ SD.h0 ≥ d + 1 - C.g :=
-- proof
  ⟨riemann_form_line_bundle C d SD, riemann_inequality_line_bundle C d SD⟩

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[serre_duality_P1_dims](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma serre_duality_P1_dims
  {n : ℤ} :
-- imply
  (max (-n - 1) 0 : ℤ) = max ((-2 - n) + 1) 0 := by
-- proof
  congr 1; ring

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[serre_duality_P1_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma serre_duality_P1_vanishing
  {n : ℤ}
-- given
  (hn : n ≥ 0) :
-- imply
  max (-n - 1) 0 = (0 : ℤ) ∧ max ((-2 - n) + 1) 0 = (0 : ℤ) := by
-- proof
  constructor
  · have : -n - 1 ≤ 0 := by linarith
    exact max_eq_right this
  · have : (-2 - n) + 1 ≤ 0 := by linarith
    exact max_eq_right this

end RiemannRochRiemannForm

namespace RiemannRochRiemannForm

/--
[serre_duality_P1_nonvanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochRiemannForm.lean)
-/
@[path]
lemma serre_duality_P1_nonvanishing
  {n : ℤ}
-- given
  (hn : n < -1) :
-- imply
  max (-n - 1) 0 > (0 : ℤ) := by
-- proof
  have : -n - 1 > 0 := by linarith
  rw [max_eq_left (by linarith : (0 : ℤ) ≤ -n - 1)]
  linarith
end RiemannRochRiemannForm



-- created on 2026-10-23
