import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorPhase
open StatMech StatMech.FrontierA


/--
[KWAdaptiveConnectorData.phase_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorPhase.lean)
-/
@[path]
private lemma phase_collapse_eq
  {a b : ℂ}
  {connector : KWAdaptiveConnectorData a b}
-- given
  (haRe : a.re ≠ 0)
  (haIm : a.im ≠ 0)
  (hbRe : b.re ≠ 0)
  (hbIm : b.im ≠ 0)
  (hsource : kwComplexCross (-a) b ≠ 0) :
-- imply
  kwVectorTurnPhase (-a) (connector.corner - a) * kwVectorTurnPhase (connector.corner - a) (b - connector.corner) * kwVectorTurnPhase (b - connector.corner) b = kwVectorTurnPhase (-a) b := by
-- proof
  apply StatMech.FrontierA.KWAdaptiveConnectorData.phase_collapse connector haRe haIm hbRe hbIm hsource


-- created on 2026-10-23
