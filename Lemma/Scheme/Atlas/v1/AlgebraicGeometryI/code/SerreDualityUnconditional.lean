import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SerreDualityUnconditional
open SerreDualityUnconditional
open TateCechInfra SerreDualityCurves
open CanonicalSheafCurves RiemannRochCurves


namespace SerreDualityUnconditional

/--
[serre_duality_numerical_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityUnconditional.lean)
-/
@[path]
lemma serre_duality_numerical_unconditional
  [Field k]
  {D : CechSheafData k} :
-- imply
  D.h1_E = D.h0_EK :=
-- proof
  (serre_duality_unconditional D).symm

end SerreDualityUnconditional

namespace SerreDualityUnconditional

/--
[genus_arithmetic_eq_geometric_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityUnconditional.lean)
-/
@[path]
lemma genus_arithmetic_eq_geometric_unconditional
  [Field k]
  {D : CechSheafData k}
  {ga gm : ℤ}
-- given
  (_hh0_O : D.h0_E = 1)
  (hga : ga = D.h1_E)
  (hgm : gm = D.h0_EK) :
-- imply
  ga = gm := by
-- proof
  rw [hga, hgm]
  exact (serre_duality_unconditional D).symm

end SerreDualityUnconditional

namespace SerreDualityUnconditional

/--
[serre_duality_both_directions_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityUnconditional.lean)
-/
@[path]
lemma serre_duality_both_directions_unconditional
  [Field k]
  {D : CechSheafData k} :
-- imply
  D.h1_E = D.h0_EK :=
-- proof
  (serre_duality_unconditional D).symm
end SerreDualityUnconditional



-- created on 2026-10-23
