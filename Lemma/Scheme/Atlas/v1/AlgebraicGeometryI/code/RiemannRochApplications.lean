import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochApplications
open CanonicalSheafCurves RiemannRochEulerCurves RiemannRochRiemannForm SheafCohCurvesFiniteness RiemannRochApplications
open SheafCohCurvesFiniteness


namespace RiemannRochApplications

/--
[corollary_29_serre_duality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma corollary_29_serre_duality
  {C : SmoothCompleteCurve}
-- given
  (_hg : C.g ≥ 0)
  (h0_O h1_O h0_K : ℤ)
  (_hchi_O : C.χ (1, 0) = h0_O - h1_O)
  (hSD_O : h1_O = h0_K)
  (_hh0_O : h0_O = 1)
  (hh1_O : h1_O = C.g) :
-- imply
  h0_K = C.g := by
-- proof
  linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[corollary_29](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma corollary_29
  {C : SmoothCompleteCurve}
-- given
  (_hg : C.g ≥ 0)
  (h0_K h1_K : ℤ)
  (hchi_K : C.χ (1, C.degK) = h0_K - h1_K)
  (hSD_K : h1_K = 1) :
-- imply
  h0_K = C.g := by
-- proof
  have := euler_char_canonical C
  linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[genus_from_canonical_sections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma genus_from_canonical_sections
  {C : SmoothCompleteCurve}
-- given
  (_hg : C.g ≥ 0)
  (h0_K h1_K : ℤ)
  (hchi_K : C.χ (1, C.degK) = h0_K - h1_K)
  (hSD_K : h1_K = 1)
  (_hh0_K : h0_K ≥ 0) :
-- imply
  h0_K = C.g := by
-- proof
  have hRR := euler_char_canonical C
  linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[corollary_29_numerical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma corollary_29_numerical
  {C : SmoothCompleteCurve} :
-- imply
  C.χ (1, 0) = 1 - C.g ∧ C.χ (1, C.degK) = C.g - 1 ∧ C.χ (1, 0) + C.χ (1, C.degK) = 0 :=
-- proof
  ⟨chi_structure_sheaf_curve C,
    euler_char_canonical C,
    serre_duality_chi C⟩

end RiemannRochApplications

namespace RiemannRochApplications

/--
[serre_dual_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma serre_dual_degree
  {C : SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  C.degK - d = (2 * C.g - 2) - d := by
-- proof
  rw [deg_canonical_eq_2g_sub_2 C]

end RiemannRochApplications

namespace RiemannRochApplications

/--
[high_degree_serre_dual_negative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma high_degree_serre_dual_negative
  {C : SmoothCompleteCurve}
  {d : ℤ}
-- given
  (hd : d > 2 * C.g - 2) :
-- imply
  C.degK - d < 0 := by
-- proof
  have := deg_canonical_eq_2g_sub_2 C
  linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[high_degree_euler_char_dual_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma high_degree_euler_char_dual_nonpos
  {C : SmoothCompleteCurve}
  {d : ℤ}
-- given
  (hd : d > 2 * C.g - 2)
  (hg : C.g ≥ 0) :
-- imply
  C.χ (1, C.degK - d) ≤ 0 := by
-- proof
  rw [euler_char_line_bundle]
  have := deg_canonical_eq_2g_sub_2 C
  linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[high_degree_exact_rr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma high_degree_exact_rr
  {C : SmoothCompleteCurve}
  {d : ℤ}
  {SD : SerreDualityCurve C 1 d}
-- given
  (h1_zero : SD.h1 = 0) :
-- imply
  SD.h0 = d + 1 - C.g := by
-- proof
  have := riemann_roch_exact_when_h1_zero C 1 d SD h1_zero
  linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[high_degree_has_sections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma high_degree_has_sections
  {C : SmoothCompleteCurve}
  {d : ℤ}
  {SD : SerreDualityCurve C 1 d}
-- given
  (hd : d ≥ 2 * C.g - 1)
  (_hg : C.g ≥ 0)
  (h1_zero : SD.h1 = 0) :
-- imply
  SD.h0 ≥ C.g := by
-- proof
  have := high_degree_exact_rr C d SD h1_zero
  linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[very_high_degree_sections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma very_high_degree_sections
  {C : SmoothCompleteCurve}
  {d : ℤ}
  {SD : SerreDualityCurve C 1 d}
-- given
  (hd : d ≥ 2 * C.g)
  (h1_zero : SD.h1 = 0) :
-- imply
  SD.h0 ≥ C.g + 1 := by
-- proof
  have := high_degree_exact_rr C d SD h1_zero
  linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[genus_zero_chi_O](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma genus_zero_chi_O
  {C : SmoothCompleteCurve}
-- given
  (hg : C.g = 0) :
-- imply
  C.χ (1, 0) = 1 := by
-- proof
  rw [chi_structure_sheaf_curve]; linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[genus_zero_deg_K](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma genus_zero_deg_K
  {C : SmoothCompleteCurve}
-- given
  (hg : C.g = 0) :
-- imply
  C.degK = -2 := by
-- proof
  have := deg_canonical_eq_2g_sub_2 C; linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[genus_zero_point_chi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma genus_zero_point_chi
  {C : SmoothCompleteCurve}
-- given
  (hg : C.g = 0) :
-- imply
  C.χ (1, 1) = 2 := by
-- proof
  rw [euler_char_line_bundle]; linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[genus_zero_point_sections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma genus_zero_point_sections
  {C : SmoothCompleteCurve}
  {SD : SerreDualityCurve C 1 1}
-- given
  (hg : C.g = 0)
  (h1_zero : SD.h1 = 0) :
-- imply
  SD.h0 = 2 := by
-- proof
  have := riemann_roch_exact_when_h1_zero C 1 1 SD h1_zero
  linarith [hg]

end RiemannRochApplications

namespace RiemannRochApplications

/--
[genus_zero_gives_map_to_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma genus_zero_gives_map_to_P1
  {C : SmoothCompleteCurve}
-- given
  (hg : C.g = 0) :
-- imply
  C.χ (1, 1) = 2 ∧ C.degK - 1 < 0 := by
-- proof
  constructor
  · exact genus_zero_point_chi C hg
  · have := genus_zero_deg_K C hg
    linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[genus_zero_sections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma genus_zero_sections
  {C : SmoothCompleteCurve}
  {d : ℤ}
  {SD : SerreDualityCurve C 1 d}
-- given
  (hg : C.g = 0)
  (h1_zero : SD.h1 = 0) :
-- imply
  SD.h0 = d + 1 := by
-- proof
  have := riemann_roch_exact_when_h1_zero C 1 d SD h1_zero
  linarith [hg]

end RiemannRochApplications

namespace RiemannRochApplications

/--
[elliptic_chi_O](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma elliptic_chi_O
  {C : SmoothCompleteCurve}
-- given
  (hg : C.g = 1) :
-- imply
  C.χ (1, 0) = 0 := by
-- proof
  rw [chi_structure_sheaf_curve]; linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[elliptic_K_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma elliptic_K_trivial
  {C : SmoothCompleteCurve}
-- given
  (hg : C.g = 1) :
-- imply
  C.degK = 0 := by
-- proof
  have := deg_canonical_eq_2g_sub_2 C; linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[elliptic_chi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma elliptic_chi
  {C : SmoothCompleteCurve}
  {d : ℤ}
-- given
  (hg : C.g = 1) :
-- imply
  C.χ (1, d) = d := by
-- proof
  rw [euler_char_line_bundle]; linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[elliptic_sections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma elliptic_sections
  {C : SmoothCompleteCurve}
  {d : ℤ}
  {SD : SerreDualityCurve C 1 d}
-- given
  (hg : C.g = 1)
  (h1_zero : SD.h1 = 0) :
-- imply
  SD.h0 = d := by
-- proof
  have := riemann_roch_exact_when_h1_zero C 1 d SD h1_zero
  linarith [hg]

end RiemannRochApplications

namespace RiemannRochApplications

/--
[elliptic_cubic_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma elliptic_cubic_embedding
  {C : SmoothCompleteCurve}
  {SD : SerreDualityCurve C 1 3}
-- given
  (hg : C.g = 1)
  (h1_zero : SD.h1 = 0) :
-- imply
  SD.h0 = 3 :=
-- proof
  elliptic_sections C hg 3 SD h1_zero

end RiemannRochApplications

namespace RiemannRochApplications

/--
[genus2_deg_K](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma genus2_deg_K
  {C : SmoothCompleteCurve}
-- given
  (hg : C.g = 2) :
-- imply
  C.degK = 2 := by
-- proof
  have := deg_canonical_eq_2g_sub_2 C; linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[genus2_canonical_sections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma genus2_canonical_sections
  {C : SmoothCompleteCurve}
  {SD : SerreDualityCurve C 1 C.degK}
-- given
  (hg : C.g = 2)
  (hSD_h1 : SD.h1 = 1) :
-- imply
  SD.h0 = 2 := by
-- proof
  have hchi := euler_char_canonical C
  have := SD.chi_decomp
  linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[genus2_high_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma genus2_high_degree
  {C : SmoothCompleteCurve}
  {d : ℤ}
  {SD : SerreDualityCurve C 1 d}
-- given
  (hg : C.g = 2)
  (h1_zero : SD.h1 = 0) :
-- imply
  SD.h0 = d - 1 := by
-- proof
  have := riemann_roch_exact_when_h1_zero C 1 d SD h1_zero
  linarith [hg]

end RiemannRochApplications

namespace RiemannRochApplications

/--
[P1_verify_H0_structure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma P1_verify_H0_structure
  {k : Type}
  [Field k] :
-- imply
  Module.finrank k (SheafCohomology.H0 k 0) = 1 :=
-- proof
SheafCohomology.finrank_H0_of_nonneg k 0 le_rfl

end RiemannRochApplications

namespace RiemannRochApplications

/--
[P1_verify_H1_structure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma P1_verify_H1_structure
  {k : Type}
  [Field k] :
-- imply
  Module.finrank k (SheafCohomology.H1 k 0) = 0 :=
-- proof
SheafCohomology.finrank_H1_of_nonneg k 0 le_rfl

end RiemannRochApplications

namespace RiemannRochApplications

/--
[P1_verify_euler_char_O](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma P1_verify_euler_char_O
  {k : Type}
  [Field k] :
-- imply
  (Module.finrank k (SheafCohomology.H0 k 0) : ℤ) - (Module.finrank k (SheafCohomology.H1 k 0) : ℤ) = 1 := by
-- proof
  rw [P1_verify_H0_structure, P1_verify_H1_structure]
  norm_num

end RiemannRochApplications

namespace RiemannRochApplications

/--
[P1_verify_serre_duality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma P1_verify_serre_duality
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  Module.finrank k (SheafCohomology.H1 k n) = Module.finrank k (SheafCohomology.H0 k (-2 - n)) := by
-- proof
  by_cases hn : 0 ≤ n
  · exact SheafCohomology.serre_duality_nonneg k n hn
  · exact SheafCohomology.serre_duality_neg k n (not_le.mp hn)

end RiemannRochApplications

namespace RiemannRochApplications

/--
[P1_verify_H0_degree1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma P1_verify_H0_degree1
  {k : Type}
  [Field k] :
-- imply
  Module.finrank k (SheafCohomology.H0 k 1) = 2 := by
-- proof
  rw [SheafCohomology.finrank_H0_of_nonneg k 1 (by norm_num)]
  simp

end RiemannRochApplications

namespace RiemannRochApplications

/--
[P1_verify_H1_degree1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma P1_verify_H1_degree1
  {k : Type}
  [Field k] :
-- imply
  Module.finrank k (SheafCohomology.H1 k 1) = 0 :=
-- proof
SheafCohomology.finrank_H1_of_nonneg k 1 (by norm_num)

end RiemannRochApplications

namespace RiemannRochApplications

/--
[P1_verify_H0_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma P1_verify_H0_nonneg
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : 0 ≤ n) :
-- imply
  (Module.finrank k (SheafCohomology.H0 k n) : ℤ) = n + 1 := by
-- proof
  rw [SheafCohomology.finrank_H0_of_nonneg k n hn]
  omega

end RiemannRochApplications

namespace RiemannRochApplications

/--
[P1_verify_H1_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma P1_verify_H1_nonneg
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : 0 ≤ n) :
-- imply
  Module.finrank k (SheafCohomology.H1 k n) = 0 :=
-- proof
SheafCohomology.finrank_H1_of_nonneg k n hn

end RiemannRochApplications

namespace RiemannRochApplications

/--
[P1_verify_H0_neg1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma P1_verify_H0_neg1
  {k : Type}
  [Field k] :
-- imply
  Module.finrank k (SheafCohomology.H0 k (-1)) = 0 :=
-- proof
SheafCohomology.finrank_H0_of_neg k (-1) (by norm_num)

end RiemannRochApplications

namespace RiemannRochApplications

/--
[P1_verify_H1_neg2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma P1_verify_H1_neg2
  {k : Type}
  [Field k] :
-- imply
  Module.finrank k (SheafCohomology.H1 k (-2)) = 1 := by
-- proof
  rw [SheafCohomology.finrank_H1_of_neg k (-2) (by norm_num)]
  norm_num

end RiemannRochApplications

namespace RiemannRochApplications

/--
[P1_abstract_cech_consistency](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma P1_abstract_cech_consistency
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  (mkCurve 0).χ (1, n) = (Module.finrank k (SheafCohomology.H0 k n) : ℤ) - (Module.finrank k (SheafCohomology.H1 k n) : ℤ) := by
-- proof
  rw [euler_char_P1 (mkCurve 0) (mkCurve_genus 0) n]
  exact (SheafCohomology.euler_characteristic k n).symm

end RiemannRochApplications

namespace RiemannRochApplications

/--
[P1_genus_consistency](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma P1_genus_consistency
  {k : Type}
  [Field k] :
-- imply
  (mkCurve 0).g = (Module.finrank k (SheafCohomology.H1 k 0) : ℤ) := by
-- proof
  rw [mkCurve_genus, P1_verify_H1_structure]

end RiemannRochApplications

namespace RiemannRochApplications

/--
[genus_from_euler_char](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma genus_from_euler_char
  {C : SmoothCompleteCurve} :
-- imply
  C.g = 1 - C.χ (1, 0) := by
-- proof
  rw [chi_structure_sheaf_curve]; ring

end RiemannRochApplications

namespace RiemannRochApplications

/--
[degree_genus_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma degree_genus_formula
  {C : SmoothCompleteCurve} :
-- imply
  C.degK + 2 = 2 * C.g := by
-- proof
  have := deg_canonical_eq_2g_sub_2 C; linarith

end RiemannRochApplications

namespace RiemannRochApplications

/--
[riemann_inequality_from_SD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma riemann_inequality_from_SD
  {C : SmoothCompleteCurve}
  {d : ℤ}
  {SD : SerreDualityCurve C 1 d} :
-- imply
  d + 1 - C.g ≤ SD.h0 :=
-- proof
riemann_inequality_line_bundle C d SD

end RiemannRochApplications

namespace RiemannRochApplications

/--
[serre_duality_euler_char](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma serre_duality_euler_char
  {C : SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  C.χ (1, d) + C.χ (1, C.degK - d) = 0 :=
-- proof
  euler_char_dual_line_bundle C d

end RiemannRochApplications

namespace RiemannRochApplications

/--
[self_dual_chi_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean)
-/
@[path]
lemma self_dual_chi_zero
  {C : SmoothCompleteCurve} :
-- imply
  C.χ (1, C.g - 1) = 0 := by
-- proof
  rw [euler_char_line_bundle]; ring

end RiemannRochApplications


-- created on 2026-10-23
