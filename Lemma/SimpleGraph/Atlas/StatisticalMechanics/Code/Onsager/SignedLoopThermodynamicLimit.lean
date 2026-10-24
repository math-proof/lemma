import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SignedLoopThermodynamicLimit
open Finset SimpleGraph MeasureTheory Filter Topology StatMech StatMech.Onsager


/--
[ons_box2EquivRect_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopThermodynamicLimit.lean)
-/
@[path]
private lemma ons_box2EquivRect_adj_eq
  {n : Nat}
  {x y : sctBox 2 n} :
-- imply
  (sctBoxGraph 2 n).Adj x y ↔ (ons_rectDualGraph (2 * n) (2 * n)).Adj (ons_box2EquivRect n x) (ons_box2EquivRect n y) := by
-- proof
  apply StatMech.Onsager.ons_box2EquivRect_adj n x y

/--
[ons_rectDualPath_twoPoint_eq_freeMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopThermodynamicLimit.lean)
-/
@[path]
private lemma ons_rectDualPath_twoPoint_eq_freeMeasure_eq
  {n : Nat}
  {beta : Real}
  {path : ons_RectDualPath (2 * n) (2 * n)} :
-- imply
  isingExpectation (ons_rectDualGraph (2 * n) (2 * n)) beta 0 (fun spin => Ising.spin spin path.source * Ising.spin spin path.target) = ∫ spin, spinProd {((ons_box2EquivRect n).symm path.source).1, ((ons_box2EquivRect n).symm path.target).1} spin ∂(freeMeasure 2 n beta 0 : Measure (ConfigSpace (Site 2))) := by
-- proof
  apply StatMech.Onsager.ons_rectDualPath_twoPoint_eq_freeMeasure n beta path

/--
[ons_rectDualPathCriticalRatio_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopThermodynamicLimit.lean)
-/
@[path]
private lemma ons_rectDualPathCriticalRatio_tendsto_freeState_eq
  {a b : Site 2}
-- given
  (embedding : ∀ n, KWStraightLineEmbedding (ons_rectDualGraph (2 * n) (2 * n)))
  (path : ∀ n, ons_RectDualPath (2 * n) (2 * n))
  (hsource : ∀ᶠ n in atTop, ((ons_box2EquivRect n).symm (path n).source).1 = a)
  (htarget : ∀ᶠ n in atTop, ((ons_box2EquivRect n).symm (path n).target).1 = b) :
-- imply
  Tendsto (fun n => ons_rectDualPathCriticalRatio (embedding n) (path n)) atTop (nhds ((((∫ spin, spinProd {a, b} spin ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.ons_rectDualPathCriticalRatio_tendsto_freeState embedding path a b hsource htarget


-- created on 2026-10-23
