import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCriticalCoupling
open Set StatMech StatMech.FrontierA


/--
[gaugeCriticalCoupling_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCriticalCoupling.lean)
-/
@[path]
private lemma gaugeCriticalCoupling_pos_eq
  {betaIsing : Real}
-- given
  (hbeta : 0 < betaIsing) :
-- imply
  0 < gaugeCriticalCoupling betaIsing := by
-- proof
  apply StatMech.FrontierA.gaugeCriticalCoupling_pos hbeta

/--
[gaugeDualCoupling_gaugeCriticalCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCriticalCoupling.lean)
-/
@[path]
private lemma gaugeDualCoupling_gaugeCriticalCoupling_eq
  {betaIsing : Real}
-- given
  (hbeta : 0 < betaIsing) :
-- imply
  gaugeDualCoupling (gaugeCriticalCoupling betaIsing) = betaIsing := by
-- proof
  apply StatMech.FrontierA.gaugeDualCoupling_gaugeCriticalCoupling hbeta

/--
[coth_gaugeCriticalCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCriticalCoupling.lean)
-/
@[path]
private lemma coth_gaugeCriticalCoupling_eq
  {betaIsing : Real}
-- given
  (hbeta : 0 < betaIsing) :
-- imply
  Real.cosh (gaugeCriticalCoupling betaIsing) / Real.sinh (gaugeCriticalCoupling betaIsing) = Real.exp (2 * betaIsing) := by
-- proof
  apply StatMech.FrontierA.coth_gaugeCriticalCoupling hbeta

/--
[gaugeDualCoupling_lt_iff_gaugeCriticalCoupling_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCriticalCoupling.lean)
-/
@[path]
private lemma gaugeDualCoupling_lt_iff_gaugeCriticalCoupling_lt_eq
  {K betaIsing : Real}
-- given
  (hK : 0 < K)
  (hbeta : 0 < betaIsing) :
-- imply
  gaugeDualCoupling K < betaIsing ↔ gaugeCriticalCoupling betaIsing < K := by
-- proof
  apply StatMech.FrontierA.gaugeDualCoupling_lt_iff_gaugeCriticalCoupling_lt hK hbeta

/--
[lt_gaugeDualCoupling_iff_lt_gaugeCriticalCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCriticalCoupling.lean)
-/
@[path]
private lemma lt_gaugeDualCoupling_iff_lt_gaugeCriticalCoupling_eq
  {K betaIsing : Real}
-- given
  (hK : 0 < K)
  (hbeta : 0 < betaIsing) :
-- imply
  betaIsing < gaugeDualCoupling K ↔ K < gaugeCriticalCoupling betaIsing := by
-- proof
  apply StatMech.FrontierA.lt_gaugeDualCoupling_iff_lt_gaugeCriticalCoupling hK hbeta


-- created on 2026-10-23
