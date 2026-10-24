import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohomology


namespace GAGA

/--
[P1_gaga_algebraic_side](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GAGA.lean)
-/
@[path]
lemma P1_gaga_algebraic_side
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  (Module.finrank k (SheafCohomology.H0 k n) : ℤ) - (Module.finrank k (SheafCohomology.H1 k n) : ℤ) = n + 1 :=
-- proof
  SheafCohomology.euler_characteristic k n

end GAGA


-- created on 2026-10-23
