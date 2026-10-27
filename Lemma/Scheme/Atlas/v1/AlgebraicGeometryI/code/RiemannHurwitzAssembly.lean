import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzAssembly
open CanonicalSheafCurves RiemannHurwitzAssembly RiemannHurwitzAssembly.CurveCovering


namespace RiemannHurwitzAssembly.CurveCovering

/--
[riemann_hurwitz_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzAssembly.lean)
-/
@[path]
lemma riemann_hurwitz_genus
  {f : CurveCovering} :
-- imply
  2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) + f.deg_R := by
-- proof
  have h_deg := f.degK_eq
  have h_X := deg_canonical_eq_2g_sub_2 f.X
  have h_Y := deg_canonical_eq_2g_sub_2 f.Y
  rw [h_X, h_Y] at h_deg
  linarith

end RiemannHurwitzAssembly.CurveCovering

namespace RiemannHurwitzAssembly.CurveCovering

/--
[riemann_hurwitz_genus_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzAssembly.lean)
-/
@[path]
lemma riemann_hurwitz_genus_explicit
  {f : CurveCovering} :
-- imply
  2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) + f.deg_R := by
-- proof
  have h_deg : f.X.degK = f.n * f.Y.degK + f.deg_R := f.degK_eq
  have h_degK_X : f.X.degK = 2 * f.X.g - 2 := deg_canonical_eq_2g_sub_2 f.X
  have h_degK_Y : f.Y.degK = 2 * f.Y.g - 2 := deg_canonical_eq_2g_sub_2 f.Y
  rw [h_degK_X, h_degK_Y] at h_deg
  linarith

end RiemannHurwitzAssembly.CurveCovering

namespace RiemannHurwitzAssembly.CurveCovering

/--
[degree_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzAssembly.lean)
-/
@[path]
lemma degree_form
  {f : CurveCovering} :
-- imply
  f.X.degK = f.n * f.Y.degK + f.deg_R :=
-- proof
  f.degK_eq

end RiemannHurwitzAssembly.CurveCovering

namespace RiemannHurwitzAssembly.CurveCovering

/--
[genus_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzAssembly.lean)
-/
@[path]
lemma genus_lower_bound
  {f : CurveCovering} :
-- imply
  f.X.g ≥ f.n * f.Y.g - f.n + 1 := by
-- proof
  have hRH := f.riemann_hurwitz_genus
  have hR := f.deg_R_nonneg
  nlinarith

end RiemannHurwitzAssembly.CurveCovering

namespace RiemannHurwitzAssembly.CurveCovering

/--
[deg_R_from_genera](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzAssembly.lean)
-/
@[path]
lemma deg_R_from_genera
  {f : CurveCovering} :
-- imply
  f.deg_R = 2 * f.X.g - 2 - f.n * (2 * f.Y.g - 2) := by
-- proof
  have hRH := f.riemann_hurwitz_genus
  linarith

end RiemannHurwitzAssembly.CurveCovering

namespace RiemannHurwitzAssembly.CurveCovering

/--
[etale_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzAssembly.lean)
-/
@[path]
lemma etale_genus
  {f : CurveCovering}
-- given
  (h : f.deg_R = 0) :
-- imply
  2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) := by
-- proof
  have hRH := f.riemann_hurwitz_genus
  linarith

end RiemannHurwitzAssembly.CurveCovering

namespace RiemannHurwitzAssembly.CurveCovering

/--
[hyperelliptic_ramification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzAssembly.lean)
-/
@[path]
lemma hyperelliptic_ramification
  {f : CurveCovering}
-- given
  (hn : f.n = 2)
  (hg : f.Y.g = 0) :
-- imply
  f.deg_R = 2 * f.X.g + 2 := by
-- proof
  have hRH := f.riemann_hurwitz_genus
  nlinarith

end RiemannHurwitzAssembly.CurveCovering

namespace RiemannHurwitzAssembly

/--
[riemann_hurwitz_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzAssembly.lean)
-/
@[path]
lemma riemann_hurwitz_theorem
  {f : CurveCovering} :
-- imply
  2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) + f.deg_R :=
-- proof
  f.riemann_hurwitz_genus

end RiemannHurwitzAssembly

namespace RiemannHurwitzAssembly

/--
[canonical_degree_eq_2g_sub_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzAssembly.lean)
-/
@[path]
lemma canonical_degree_eq_2g_sub_2
  {C : SmoothCompleteCurve} :
-- imply
  C.degK = 2 * C.g - 2 :=
-- proof
  deg_canonical_eq_2g_sub_2 C

end RiemannHurwitzAssembly

namespace RiemannHurwitzAssembly

/--
[riemann_hurwitz_from_A1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzAssembly.lean)
-/
@[path]
lemma riemann_hurwitz_from_A1
  {f : CurveCovering} :
-- imply
  2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) + f.deg_R :=
-- proof
  riemann_hurwitz_formula f.n f.X.g f.Y.g f.deg_R f.X.degK f.Y.degK
    (f.n * f.Y.degK)
    (deg_canonical_eq_2g_sub_2 f.X)
    (deg_canonical_eq_2g_sub_2 f.Y)
    rfl
    f.degK_eq

end RiemannHurwitzAssembly


-- created on 2026-10-23
