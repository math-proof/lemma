import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectEndpoint
open MeasureTheory Filter Topology StatMech StatMech.Onsager


/--
[ons_canonicalRectDualPathRatio_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectEndpoint.lean)
-/
@[path]
private lemma ons_canonicalRectDualPathRatio_tendsto_freeState_eq
  {beta : Real}
  {a b : Site 2}
-- given
  (hbeta : 0 < beta)
  (path : ∀ n, ons_RectDualPath (2 * n) (2 * n))
  (hsource : ∀ᶠ n in atTop, ((ons_box2EquivRect n).symm (path n).source).1 = a)
  (htarget : ∀ᶠ n in atTop, ((ons_box2EquivRect n).symm (path n).target).1 = b) :
-- imply
  Tendsto (fun n => ons_rectDualPathRatio (ons_rectDualStraightLineEmbedding (2 * n) (2 * n)) (path n) beta) atTop (nhds ((((∫ spin, spinProd {a, b} spin ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.ons_canonicalRectDualPathRatio_tendsto_freeState beta hbeta path a b hsource htarget

/--
[ons_canonicalRectDualPathCriticalRatio_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectEndpoint.lean)
-/
@[path]
private lemma ons_canonicalRectDualPathCriticalRatio_tendsto_freeState_eq
  {a b : Site 2}
-- given
  (path : ∀ n, ons_RectDualPath (2 * n) (2 * n))
  (hsource : ∀ᶠ n in atTop, ((ons_box2EquivRect n).symm (path n).source).1 = a)
  (htarget : ∀ᶠ n in atTop, ((ons_box2EquivRect n).symm (path n).target).1 = b) :
-- imply
  Tendsto (fun n => ons_rectDualPathCriticalRatio (ons_rectDualStraightLineEmbedding (2 * n) (2 * n)) (path n)) atTop (nhds ((((∫ spin, spinProd {a, b} spin ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.ons_canonicalRectDualPathCriticalRatio_tendsto_freeState path a b hsource htarget


-- created on 2026-10-23
