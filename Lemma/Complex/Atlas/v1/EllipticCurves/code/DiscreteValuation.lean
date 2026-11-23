import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.EllipticCurves.code.DiscreteValuation
open DiscreteValuation


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



-- created on 2026-10-23
-- updated on 2026-11-22
