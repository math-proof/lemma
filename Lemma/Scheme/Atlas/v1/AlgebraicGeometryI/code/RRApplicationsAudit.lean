import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RRApplicationsAudit
open CanonicalSheafCurves RiemannRochEulerCurves RiemannRochRiemannForm RiemannRochApplications SheafCohCurvesFiniteness RRApplicationsAudit
open RiemannRochApplications SheafCohCurvesFiniteness


namespace RRApplicationsAudit

/--
[audit_degK_derivation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RRApplicationsAudit.lean)
-/
@[path]
lemma audit_degK_derivation
  {C : SmoothCompleteCurve} :
-- imply
  C.degK = 2 * C.g - 2 :=
-- proof
  deg_canonical_eq_2g_sub_2 C

end RRApplicationsAudit

namespace RRApplicationsAudit

/--
[audit_riemann_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RRApplicationsAudit.lean)
-/
@[path]
lemma audit_riemann_inequality
  {C : SmoothCompleteCurve}
  {d : ℤ}
  {SD : SerreDualityCurve C 1 d} :
-- imply
  SD.h0 ≥ d + 1 - C.g :=
-- proof
  riemann_inequality_line_bundle C d SD

end RRApplicationsAudit

namespace RRApplicationsAudit

/--
[audit_corollary_29](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RRApplicationsAudit.lean)
-/
@[path]
lemma audit_corollary_29
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

end RRApplicationsAudit

namespace RRApplicationsAudit

/--
[audit_high_degree_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RRApplicationsAudit.lean)
-/
@[path]
lemma audit_high_degree_exact
  {C : SmoothCompleteCurve}
  {d : ℤ}
  {SD : SerreDualityCurve C 1 d}
-- given
  (h1_zero : SD.h1 = 0) :
-- imply
  SD.h0 = d + 1 - C.g :=
-- proof
  high_degree_exact_rr C d SD h1_zero

end RRApplicationsAudit

namespace RRApplicationsAudit

/--
[audit_genus_zero_sections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RRApplicationsAudit.lean)
-/
@[path]
lemma audit_genus_zero_sections
  {C : SmoothCompleteCurve}
  {SD : SerreDualityCurve C 1 1}
-- given
  (hg : C.g = 0)
  (h1_zero : SD.h1 = 0) :
-- imply
  SD.h0 = 2 :=
-- proof
  genus_zero_point_sections C hg SD h1_zero

end RRApplicationsAudit

namespace RRApplicationsAudit

/--
[audit_serre_duality_chi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RRApplicationsAudit.lean)
-/
@[path]
lemma audit_serre_duality_chi
  {C : SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  C.χ (1, d) + C.χ (1, C.degK - d) = 0 :=
-- proof
  euler_char_dual_line_bundle C d

end RRApplicationsAudit

namespace RRApplicationsAudit

/--
[audit_P1_consistency](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RRApplicationsAudit.lean)
-/
@[path]
lemma audit_P1_consistency
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  (mkCurve 0).χ (1, n) = (Module.finrank k (SheafCohomology.H0 k n) : ℤ) - (Module.finrank k (SheafCohomology.H1 k n) : ℤ) :=
-- proof
  P1_abstract_cech_consistency k n

end RRApplicationsAudit

namespace RRApplicationsAudit

/--
[audit_dedekind_grounding](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RRApplicationsAudit.lean)
-/
@[path]
lemma audit_dedekind_grounding
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.toSmoothCompleteCurve.g = (C.ddGenus : ℤ) := by
-- proof
  rfl

end RRApplicationsAudit

namespace RRApplicationsAudit

/--
[audit_dedekind_SD_O](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RRApplicationsAudit.lean)
-/
@[path]
lemma audit_dedekind_SD_O
  [Field k]
  {C : DedekindCurve k} :
-- imply
  (serreDualityO_fromDedekind C).h0 = 1 ∧ (serreDualityO_fromDedekind C).h1 = (C.ddGenus : ℤ) :=
-- proof
⟨rfl, rfl⟩

end RRApplicationsAudit

namespace RRApplicationsAudit

/--
[audit_full_pipeline_genus0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RRApplicationsAudit.lean)
-/
@[path]
lemma audit_full_pipeline_genus0
  {C : SmoothCompleteCurve}
  {SD : SerreDualityCurve C 1 1}
-- given
  (hg : C.g = 0)
  (h1_zero : SD.h1 = 0) :
-- imply
  SD.h0 = 2 ∧ C.degK = -2 ∧ C.χ (1, 0) = 1 := by
-- proof
  refine ⟨?_, ?_, ?_⟩
  · exact genus_zero_point_sections C hg SD h1_zero
  · exact genus_zero_deg_K C hg
  · exact genus_zero_chi_O C hg

end RRApplicationsAudit

namespace RRApplicationsAudit

/--
[audit_full_pipeline_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RRApplicationsAudit.lean)
-/
@[path]
lemma audit_full_pipeline_general
  {C : SmoothCompleteCurve}
  {d : ℤ}
  {SD : SerreDualityCurve C 1 d} :
-- imply
  SD.h0 ≥ d + 1 - C.g ∧ C.χ (1, d) + C.χ (1, C.degK - d) = 0 ∧ C.degK = 2 * C.g - 2 := by
-- proof
  refine ⟨?_, ?_, ?_⟩
  · exact riemann_inequality_line_bundle C d SD
  · exact euler_char_dual_line_bundle C d
  · exact deg_canonical_eq_2g_sub_2 C

end RRApplicationsAudit

namespace RRApplicationsAudit

/--
[audit_elliptic_pipeline](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RRApplicationsAudit.lean)
-/
@[path]
lemma audit_elliptic_pipeline
  {C : SmoothCompleteCurve}
  {SD3 : SerreDualityCurve C 1 3}
-- given
  (hg : C.g = 1)
  (h1_zero : SD3.h1 = 0) :
-- imply
  C.χ (1, 0) = 0 ∧ C.degK = 0 ∧ SD3.h0 = 3 := by
-- proof
  refine ⟨?_, ?_, ?_⟩
  · exact elliptic_chi_O C hg
  · exact elliptic_K_trivial C hg
  · exact elliptic_cubic_embedding C hg SD3 h1_zero
end RRApplicationsAudit



-- created on 2026-10-23
