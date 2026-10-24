import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzDegree
open RiemannHurwitzFormula CanonicalSheafCurves RiemannHurwitzDegree


namespace RiemannHurwitzDegree

/--
[riemann_hurwitz_genus_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma riemann_hurwitz_genus_form
  {f : CurveCoverData}
-- given
  (h_decomp : f.morphism.deg_KX = f.morphism.degree * f.morphism.deg_KY + f.morphism.deg_R) :
-- imply
  2 * f.source.g - 2 = f.morphism.degree * (2 * f.target.g - 2) + f.morphism.deg_R := by
-- proof
  have hX := deg_canonical_eq_2g_sub_2 f.source
  have hY := deg_canonical_eq_2g_sub_2 f.target
  rw [f.h_degK_X, hX] at h_decomp
  rw [f.h_degK_Y, hY] at h_decomp
  linarith

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[riemann_hurwitz_genus_solve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma riemann_hurwitz_genus_solve
  {f : CurveCoverData}
-- given
  (h_decomp : f.morphism.deg_KX = f.morphism.degree * f.morphism.deg_KY + f.morphism.deg_R) :
-- imply
  2 * f.source.g = f.morphism.degree * (2 * f.target.g - 2) + f.morphism.deg_R + 2 := by
-- proof
  have := riemann_hurwitz_genus_form f h_decomp
  linarith

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[riemann_hurwitz_genus_lower_bound_cover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma riemann_hurwitz_genus_lower_bound_cover
  {f : CurveCoverData}
-- given
  (h_decomp : f.morphism.deg_KX = f.morphism.degree * f.morphism.deg_KY + f.morphism.deg_R) :
-- imply
  2 * f.source.g - 2 ≥ f.morphism.degree * (2 * f.target.g - 2) := by
-- proof
  have hRH := riemann_hurwitz_genus_form f h_decomp
  linarith [f.morphism.h_deg_R_nonneg]

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[riemann_hurwitz_P1_genus_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma riemann_hurwitz_P1_genus_form
  {g_X n degR : ℤ}
-- given
  (h_RH : 2 * g_X - 2 = n * (2 * 0 - 2) + degR) :
-- imply
  2 * g_X - 2 = -2 * n + degR := by
-- proof
linarith

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[riemann_hurwitz_P1_genus_solve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma riemann_hurwitz_P1_genus_solve
  {g n degR : ℤ}
-- given
  (h_RH : 2 * g - 2 = -2 * n + degR) :
-- imply
  2 * g = degR - 2 * n + 2 := by
-- proof
linarith

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[simple_ramification_degR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma simple_ramification_degR
  {r : ℤ} :
-- imply
  r * ((2 : ℤ) - 1) = r := by
-- proof
ring

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[riemann_hurwitz_simple_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma riemann_hurwitz_simple_genus
  {g n r : ℤ}
-- given
  (h_RH : 2 * g - 2 = -2 * n + r * (2 - 1)) :
-- imply
  2 * g - 2 = -2 * n + r := by
-- proof
linarith

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[simple_ramification_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma simple_ramification_count
  {g n r : ℤ}
-- given
  (h_RH : 2 * g - 2 = -2 * n + r) :
-- imply
  r = 2 * g + 2 * n - 2 := by
-- proof
linarith
section GenusComputations

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[genus_hyperelliptic_from_curves](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma genus_hyperelliptic_from_curves
  {g : ℕ} :
-- imply
  let X := mkCurve g let Y := mkCurve 0 2 * X.g - 2 = 2 * (2 * Y.g - 2) + (2 * (g : ℤ) + 2) := by
-- proof
  simp [mkCurve]
  ring

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[hyperelliptic_genus_from_branch_points](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma hyperelliptic_genus_from_branch_points
  {g b : ℤ}
-- given
  (h_RH : 2 * g - 2 = 2 * (-2 : ℤ) + b) :
-- imply
  2 * g = b - 2 := by
-- proof
linarith

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[genus_plane_quartic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma genus_plane_quartic
-- imply
  let d : ℤ := 4 let g : ℤ := 3 2 * g - 2 = d * (d - 3) := by
-- proof
norm_num

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[plane_quartic_degK](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma plane_quartic_degK
-- imply
  (4 : ℤ) * (4 - 3) = 2 * 3 - 2 := by
-- proof
norm_num

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[plane_quartic_as_cover_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma plane_quartic_as_cover_P1
-- imply
  (2 : ℤ) * 3 - 2 = -2 * 4 + 12 := by
-- proof
norm_num

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[plane_quartic_ramification_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma plane_quartic_ramification_count
-- imply
  2 * (3 : ℤ) + 2 * 4 - 2 = 12 := by
-- proof
norm_num

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[genus_plane_quintic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma genus_plane_quintic
-- imply
  let d : ℤ := 5 let g : ℤ := 6 2 * g - 2 = d * (d - 3) := by
-- proof
norm_num

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[genus_degree3_cover_4_total_ram](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma genus_degree3_cover_4_total_ram
-- imply
  let n : ℤ := 3 let r : ℤ := 4 let e : ℤ := 3 let degR := r * (e - 1) let g : ℤ := 2 2 * g - 2 = -2 * n + degR := by
-- proof
norm_num

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[genus_degree3_cover_6_simple_ram](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma genus_degree3_cover_6_simple_ram
-- imply
  let n : ℤ := 3 let degR : ℤ := 6 let g : ℤ := 1 2 * g - 2 = -2 * n + degR := by
-- proof
norm_num

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[genus_unramified_double_cover_genus2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma genus_unramified_double_cover_genus2
-- imply
  let C_X := mkCurve 3 let C_Y := mkCurve 2 2 * C_X.g - 2 = 2 * (2 * C_Y.g - 2) + 0 := by
-- proof
  simp [mkCurve]

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[genus_etale_cover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma genus_etale_cover
  {g_X g_Y n : ℤ}
-- given
  (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2)) :
-- imply
  g_X = n * (g_Y - 1) + 1 := by
-- proof
linarith
section LurothBound

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[luroth_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma luroth_bound
  {n degR : ℤ}
  {g_X : ℤ}
-- given
  (hg : g_X ≥ 0)
  (h_RH : 2 * g_X - 2 = -2 * n + degR) :
-- imply
  degR ≥ 2 * n - 2 := by
-- proof
linarith

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[luroth_bound_alt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma luroth_bound_alt
  {n degR : ℤ}
  {g_X : ℤ}
-- given
  (hg : g_X ≥ 0)
  (h_RH : 2 * g_X - 2 = -2 * n + degR) :
-- imply
  degR ≥ 2 * (n - 1) := by
-- proof
linarith

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[genus_nonneg_constraint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma genus_nonneg_constraint
  {g_X n degR : ℤ}
-- given
  (hg_X : g_X ≥ 0)
  (h_RH : 2 * g_X - 2 = -2 * n + degR) :
-- imply
  degR ≥ 2 * n - 2 := by
-- proof
linarith

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[hyperelliptic_min_branch_points](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma hyperelliptic_min_branch_points
  {g_X : ℤ}
  {b : ℤ}
-- given
  (hg : g_X ≥ 0)
  (h_RH : 2 * g_X - 2 = 2 * (-2 : ℤ) + b) :
-- imply
  b ≥ 2 := by
-- proof
linarith

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[degree3_min_ramification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma degree3_min_ramification
  {g_X : ℤ}
  {degR : ℤ}
-- given
  (hg : g_X ≥ 0)
  (h_RH : 2 * g_X - 2 = -2 * 3 + degR) :
-- imply
  degR ≥ 4 := by
-- proof
linarith

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[riemann_hurwitz_parity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma riemann_hurwitz_parity
  {g_X g_Y n degR : ℤ}
-- given
  (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + degR) :
-- imply
  ∃ k : ℤ, degR = 2 * k := by
-- proof
  use g_X - 1 - n * (g_Y - 1)
  linarith

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[ellipticCoverP1_source_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma ellipticCoverP1_source_genus
-- imply
  ellipticCoverP1.source.g = 1 := by
-- proof
  simp [ellipticCoverP1, CurveCoverData.mk', mkCurve]

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[ellipticCoverP1_target_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma ellipticCoverP1_target_genus
-- imply
  ellipticCoverP1.target.g = 0 := by
-- proof
  simp [ellipticCoverP1, CurveCoverData.mk', mkCurve]

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[ellipticCoverP1_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma ellipticCoverP1_degree
-- imply
  ellipticCoverP1.morphism.degree = 2 := by
-- proof
  simp [ellipticCoverP1, CurveCoverData.mk']

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[ellipticCoverP1_degR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma ellipticCoverP1_degR
-- imply
  ellipticCoverP1.morphism.deg_R = 4 := by
-- proof
  simp [ellipticCoverP1, CurveCoverData.mk']

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[ellipticCoverP1_RH](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma ellipticCoverP1_RH
-- imply
  2 * ellipticCoverP1.source.g - 2 = ellipticCoverP1.morphism.degree * (2 * ellipticCoverP1.target.g - 2) + ellipticCoverP1.morphism.deg_R :=
-- proof
  riemann_hurwitz_genus_form ellipticCoverP1 (by simp [ellipticCoverP1, CurveCoverData.mk', mkCurve])

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[genus2CoverP1_source_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma genus2CoverP1_source_genus
-- imply
  genus2CoverP1.source.g = 2 := by
-- proof
  simp [genus2CoverP1, CurveCoverData.mk', mkCurve]

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[genus2CoverP1_RH](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma genus2CoverP1_RH
-- imply
  2 * genus2CoverP1.source.g - 2 = genus2CoverP1.morphism.degree * (2 * genus2CoverP1.target.g - 2) + genus2CoverP1.morphism.deg_R :=
-- proof
  riemann_hurwitz_genus_form genus2CoverP1 (by simp [genus2CoverP1, CurveCoverData.mk', mkCurve])

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[genus3CoverP1_RH](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma genus3CoverP1_RH
-- imply
  2 * genus3CoverP1.source.g - 2 = genus3CoverP1.morphism.degree * (2 * genus3CoverP1.target.g - 2) + genus3CoverP1.morphism.deg_R :=
-- proof
  riemann_hurwitz_genus_form genus3CoverP1 (by simp [genus3CoverP1, CurveCoverData.mk', mkCurve])

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[hyperellipticCover_source_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma hyperellipticCover_source_genus
  {g : ℕ} :
-- imply
  (hyperellipticCover g).source.g = (g : ℤ) := by
-- proof
  simp [hyperellipticCover, CurveCoverData.mk', mkCurve]

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[hyperellipticCover_target_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma hyperellipticCover_target_genus
  {g : ℕ} :
-- imply
  (hyperellipticCover g).target.g = 0 := by
-- proof
  simp [hyperellipticCover, CurveCoverData.mk', mkCurve]

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[hyperellipticCover_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma hyperellipticCover_degree
  {g : ℕ} :
-- imply
  (hyperellipticCover g).morphism.degree = 2 := by
-- proof
  simp [hyperellipticCover, CurveCoverData.mk']

end RiemannHurwitzDegree

namespace RiemannHurwitzDegree

/--
[hyperellipticCover_degR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma hyperellipticCover_degR
  {g : ℕ} :
-- imply
  (hyperellipticCover g).morphism.deg_R = 2 * (g : ℤ) + 2 := by
-- proof
  simp [hyperellipticCover, CurveCoverData.mk']

end RiemannHurwitzDegree

/--
[riemann_hurwitz_degree_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean)
-/
@[path]
lemma riemann_hurwitz_degree_formula
  {f : CurveCovering} :
-- imply
  f.X.degK = f.n * f.Y.degK + f.deg_R :=
-- proof
  f.degK_eq


-- created on 2026-10-23
