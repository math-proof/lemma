import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SignedLoopThermodynamicGeneral
open Finset SimpleGraph MeasureTheory Filter Topology StatMech StatMech.Onsager


/--
[ons_rectDualPathRatio_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopThermodynamicGeneral.lean)
-/
@[path]
private lemma ons_rectDualPathRatio_tendsto_freeState_eq
  {beta : Real}
  {a b : Site 2}
-- given
  (hbeta : 0 < beta)
  (embedding : ∀ n, KWStraightLineEmbedding (ons_rectDualGraph (2 * n) (2 * n)))
  (path : ∀ n, ons_RectDualPath (2 * n) (2 * n))
  (hsource : ∀ᶠ n in atTop, ((ons_box2EquivRect n).symm (path n).source).1 = a)
  (htarget : ∀ᶠ n in atTop, ((ons_box2EquivRect n).symm (path n).target).1 = b) :
-- imply
  Tendsto (fun n => ons_rectDualPathRatio (embedding n) (path n) beta) atTop (nhds ((((∫ spin, spinProd {a, b} spin ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.ons_rectDualPathRatio_tendsto_freeState beta hbeta embedding path a b hsource htarget


-- created on 2026-10-23
