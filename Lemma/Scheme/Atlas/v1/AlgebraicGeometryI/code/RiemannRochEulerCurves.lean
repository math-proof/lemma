import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannRochEulerCurves
open RiemannRochCurves CanonicalSheafCurves RiemannRochEulerCurves


namespace RiemannRochEulerCurves

/--
[chi_rr_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma chi_rr_curve
  {C : SmoothCompleteCurve}
  {r d : ℤ} :
-- imply
  C.χ (r, d) = d + r * (1 - C.g) := by
-- proof
  have := chi_eq_rr C r d
  linarith

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[chi_rr_curve_alt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma chi_rr_curve_alt
  {C : SmoothCompleteCurve}
  {r d : ℤ} :
-- imply
  C.χ (r, d) = d - r * (C.g - 1) :=
-- proof
  chi_eq_rr C r d

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_additive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_additive
  {C : SmoothCompleteCurve}
  {a b : ℤ × ℤ} :
-- imply
  C.χ (a + b) = C.χ a + C.χ b :=
-- proof
  map_add C.χ a b

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_neg
  {C : SmoothCompleteCurve}
  {a : ℤ × ℤ} :
-- imply
  C.χ (-a) = -(C.χ a) :=
-- proof
  map_neg C.χ a

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_zsmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_zsmul
  {C : SmoothCompleteCurve}
  {n : ℤ}
  {a : ℤ × ℤ} :
-- imply
  C.χ (n • a) = n • (C.χ a) :=
-- proof
  map_zsmul C.χ n a

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_zero
  {C : SmoothCompleteCurve} :
-- imply
  C.χ 0 = 0 :=
-- proof
  map_zero C.χ

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_determines_chi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_determines_chi
  {C : SmoothCompleteCurve}
  {f : ℤ × ℤ →+ ℤ}
-- given
  (hf_struct : f (1, 0) = 1 - C.g)
  (hf_sky : f (0, 1) = 1) :
-- imply
  ∀ p : ℤ × ℤ, f p = C.χ p := by
-- proof
  intro ⟨r, d⟩
  have hf := riemann_roch_curves_thm C.g f hf_struct hf_sky r d
  rw [hf, ← chi_eq_rr C r d]

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_skyscraper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_skyscraper
  {C : SmoothCompleteCurve} :
-- imply
  C.χ (0, 1) = 1 :=
-- proof
  C.hχ_sky

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_line_bundle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_line_bundle
  {C : SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  C.χ (1, d) = d + 1 - C.g := by
-- proof
  have := chi_rr_curve C 1 d; linarith

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_torsion
  {C : SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  C.χ (0, d) = d := by
-- proof
  have := chi_rr_curve C 0 d; linarith

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_free
  {C : SmoothCompleteCurve}
  {r : ℤ} :
-- imply
  C.χ (r, 0) = r * (1 - C.g) := by
-- proof
  have := chi_rr_curve C r 0; linarith

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_twist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_twist
  {C : SmoothCompleteCurve}
  {r d n : ℤ} :
-- imply
  C.χ (r, d + n * r) = C.χ (r, d) + n * r := by
-- proof
  rw [chi_rr_curve C r (d + n * r), chi_rr_curve C r d]
  ring

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_dual_line_bundle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_dual_line_bundle
  {C : SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  C.χ (1, d) + C.χ (1, C.degK - d) = 0 := by
-- proof
  rw [euler_char_line_bundle C d, euler_char_line_bundle C (C.degK - d)]
  have hK := deg_canonical_eq_2g_sub_2 C
  linarith

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_serre_O_K](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_serre_O_K
  {C : SmoothCompleteCurve} :
-- imply
  C.χ (1, 0) + C.χ (1, C.degK) = 0 :=
-- proof
  serre_duality_chi C

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[h0_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma h0_lower_bound
  {C : SmoothCompleteCurve}
-- given
  (d h0 h1 : ℤ)
  (hchi : C.χ (1, d) = h0 - h1)
  (hh1 : h1 ≥ 0) :
-- imply
  h0 ≥ d + 1 - C.g := by
-- proof
  have hRR := euler_char_line_bundle C d
  linarith

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[h0_of_vanishing_h1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma h0_of_vanishing_h1
  {C : SmoothCompleteCurve}
-- given
  (d h0 : ℤ)
  (hchi : C.χ (1, d) = h0) :
-- imply
  h0 = d + 1 - C.g := by
-- proof
  have := euler_char_line_bundle C d
  linarith

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_positive_slope](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_positive_slope
  {C : SmoothCompleteCurve}
  {r d : ℤ}
-- given
  (_hr : r > 0)
  (hd : d > r * (C.g - 1)) :
-- imply
  C.χ (r, d) > 0 := by
-- proof
  rw [chi_rr_curve_alt C r d]
  linarith

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_canonical_from_rr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_canonical_from_rr
  {C : SmoothCompleteCurve} :
-- imply
  C.degK + 1 - C.g = C.g - 1 :=
-- proof
  chi_canonical_from_degree C

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_P1
  {C : SmoothCompleteCurve}
  {d : ℤ}
-- given
  (hg : C.g = 0) :
-- imply
  C.χ (1, d) = d + 1 := by
-- proof
  rw [euler_char_line_bundle]; linarith

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_elliptic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_elliptic
  {C : SmoothCompleteCurve}
  {d : ℤ}
-- given
  (hg : C.g = 1) :
-- imply
  C.χ (1, d) = d := by
-- proof
  rw [euler_char_line_bundle]; linarith

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_genus2_O](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_genus2_O
  {C : SmoothCompleteCurve}
-- given
  (hg : C.g = 2) :
-- imply
  C.χ (1, 0) = -1 := by
-- proof
  rw [chi_structure_sheaf_curve]; linarith

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[mkCurve_euler_char](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma mkCurve_euler_char
  {g : ℕ}
  {r d : ℤ} :
-- imply
  (mkCurve g).χ (r, d) = d + r * (1 - (g : ℤ)) := by
-- proof
  have h := chi_rr_curve (mkCurve g) r d
  simp only [mkCurve_genus] at h
  linarith

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_degree_shift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_degree_shift
  {C : SmoothCompleteCurve}
  {r d : ℤ} :
-- imply
  C.χ (r, d + 1) = C.χ (r, d) + 1 := by
-- proof
  rw [chi_rr_curve C r (d + 1), chi_rr_curve C r d]
  ring

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_rank_shift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_rank_shift
  {C : SmoothCompleteCurve}
  {r d : ℤ} :
-- imply
  C.χ (r + 1, d) = C.χ (r, d) + (1 - C.g) := by
-- proof
  rw [chi_rr_curve C (r + 1) d, chi_rr_curve C r d]
  ring

end RiemannRochEulerCurves

namespace RiemannRochEulerCurves

/--
[euler_char_minus_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
lemma euler_char_minus_trivial
  {C : SmoothCompleteCurve}
  {r d : ℤ} :
-- imply
  C.χ (r, d) - C.χ (r, 0) = d := by
-- proof
  rw [chi_rr_curve C r d, chi_rr_curve C r 0]
  ring
end RiemannRochEulerCurves


/--
[chi_structure_sheaf_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
private lemma chi_structure_sheaf_curve_eq
  {C : SmoothCompleteCurve} :
-- imply
  C.χ (1, 0) = 1 - C.g := by
-- proof
  apply RiemannRochEulerCurves.chi_structure_sheaf_curve C

/--
[euler_char_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean)
-/
@[path]
private lemma euler_char_canonical_eq
  {C : SmoothCompleteCurve} :
-- imply
  C.χ (1, C.degK) = C.g - 1 := by
-- proof
  apply RiemannRochEulerCurves.euler_char_canonical C


-- created on 2026-10-23
