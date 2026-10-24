import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
open StatMech StatMech.FrontierA


/--
[kwFiniteSimplePolygonPhaseSign_adaptive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveClosure.lean)
-/
@[path]
private lemma kwFiniteSimplePolygonPhaseSign_adaptive_eq :
-- imply
  KWFiniteSimplePolygonPhaseSign := by
-- proof
  apply StatMech.FrontierA.kwFiniteSimplePolygonPhaseSign_adaptive

/--
[kwStraightLineCyclePhaseSign_adaptive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveClosure.lean)
-/
@[path]
private lemma kwStraightLineCyclePhaseSign_adaptive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G} :
-- imply
  KWStraightLineCyclePhaseSign G embedding := by
-- proof
  apply StatMech.FrontierA.kwStraightLineCyclePhaseSign_adaptive embedding

/--
[kwStraightLineCycleOddTurning_adaptive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveClosure.lean)
-/
@[path]
private lemma kwStraightLineCycleOddTurning_adaptive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G} :
-- imply
  KWStraightLineCycleOddTurning G embedding := by
-- proof
  apply StatMech.FrontierA.kwStraightLineCycleOddTurning_adaptive embedding

/--
[kacWard_straightLine_trivalent_adaptive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveClosure.lean)
-/
@[path]
private lemma kacWard_straightLine_trivalent_adaptive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3) :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_straightLine_trivalent_adaptive G embedding hdeg weight


-- created on 2026-10-23
