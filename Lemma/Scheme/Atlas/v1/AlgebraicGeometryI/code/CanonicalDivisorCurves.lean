import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CanonicalDivisorCurves
open CanonicalSheafCurves CanonicalDivisorCurves


namespace CanonicalDivisorCurves

/--
[canonical_degree_eq_2g_minus_2_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorCurves.lean)
-/
@[path]
lemma canonical_degree_eq_2g_minus_2_dedekind
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.toSmoothCompleteCurve.degK = 2 * C.toSmoothCompleteCurve.g - 2 :=
-- proof
  deg_canonical_eq_2g_sub_2 C.toSmoothCompleteCurve

end CanonicalDivisorCurves

namespace CanonicalDivisorCurves

/--
[canonical_chi_eq_g_minus_1_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorCurves.lean)
-/
@[path]
lemma canonical_chi_eq_g_minus_1_dedekind
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.toSmoothCompleteCurve.χ (1, C.toSmoothCompleteCurve.degK) = C.toSmoothCompleteCurve.g - 1 :=
-- proof
  C.toSmoothCompleteCurve.hχ_canonical

end CanonicalDivisorCurves

namespace CanonicalDivisorCurves

/--
[structure_chi_eq_1_minus_g_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorCurves.lean)
-/
@[path]
lemma structure_chi_eq_1_minus_g_dedekind
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.toSmoothCompleteCurve.χ (1, 0) = 1 - C.toSmoothCompleteCurve.g :=
-- proof
  C.toSmoothCompleteCurve.hχ_struct

end CanonicalDivisorCurves

namespace CanonicalDivisorCurves

/--
[serre_duality_chi_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorCurves.lean)
-/
@[path]
lemma serre_duality_chi_dedekind
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.toSmoothCompleteCurve.χ (1, 0) + C.toSmoothCompleteCurve.χ (1, C.toSmoothCompleteCurve.degK) = 0 :=
-- proof
  serre_duality_chi C.toSmoothCompleteCurve

end CanonicalDivisorCurves

namespace CanonicalDivisorCurves

/--
[rr_formula_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorCurves.lean)
-/
@[path]
lemma rr_formula_dedekind
  [Field k]
  {C : DedekindCurve k}
  {r d : ℤ} :
-- imply
  C.toSmoothCompleteCurve.χ (r, d) = d - r * (C.toSmoothCompleteCurve.g - 1) :=
-- proof
  chi_eq_rr C.toSmoothCompleteCurve r d

end CanonicalDivisorCurves

namespace CanonicalDivisorCurves

/--
[toSCC_degK_eq_dedekind_degK](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorCurves.lean)
-/
@[path]
lemma toSCC_degK_eq_dedekind_degK
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.toSmoothCompleteCurve.degK = C.degK :=
-- proof
  rfl

end CanonicalDivisorCurves

namespace CanonicalDivisorCurves

/--
[toSCC_g_eq_ddGenus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorCurves.lean)
-/
@[path]
lemma toSCC_g_eq_ddGenus
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.toSmoothCompleteCurve.g = (C.ddGenus : ℤ) :=
-- proof
  rfl
end CanonicalDivisorCurves



-- created on 2026-10-23
