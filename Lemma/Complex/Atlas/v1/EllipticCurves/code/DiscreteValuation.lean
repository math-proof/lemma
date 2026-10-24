import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.DiscreteValuation
open DiscreteValuation


namespace DiscreteValuation

/--
[isPrincipalIdealRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DiscreteValuation.lean)
-/
@[path]
lemma isPrincipalIdealRing
  [Field F]
  {v : DiscreteValuation F} :
-- imply
  IsPrincipalIdealRing v.valuationSubring :=
-- proof
  Valuation.valuationSubring_isPrincipalIdealRing v.val

end DiscreteValuation


-- created on 2026-10-23
