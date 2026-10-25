import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceClosure
open StatMech StatMech.FrontierA


/--
[kwAngularSplitCyclePhaseSign_adaptive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardArbitraryValenceClosure.lean)
-/
@[path]
private lemma kwAngularSplitCyclePhaseSign_adaptive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G} :
-- imply
  KWAngularSplitCyclePhaseSign embedding := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitCyclePhaseSign_adaptive embedding

/--
[kacWard_straightLine_arbitrary_adaptive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardArbitraryValenceClosure.lean)
-/
@[path]
private lemma kacWard_straightLine_arbitrary_adaptive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ} :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_straightLine_arbitrary_adaptive G embedding weight


-- created on 2026-10-23
