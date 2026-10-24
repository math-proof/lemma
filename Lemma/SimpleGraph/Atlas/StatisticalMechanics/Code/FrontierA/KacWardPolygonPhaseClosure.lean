import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardPolygonPhaseClosure
open SimpleGraph StatMech StatMech.FrontierA


/--
[KWStraightLineCyclePhaseSign.of_cleanChordCompatibility](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPhaseClosure.lean)
-/
@[path]
private lemma of_cleanChordCompatibility_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hcompat : KWCleanChordPhaseCompatibility) :
-- imply
  KWStraightLineCyclePhaseSign G embedding := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCyclePhaseSign.of_cleanChordCompatibility hcompat embedding

/--
[KWStraightLineCycleOddTurning.of_cleanChordCompatibility](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPhaseClosure.lean)
-/
@[path]
private lemma of_cleanChordCompatibility_eq_2
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hcompat : KWCleanChordPhaseCompatibility) :
-- imply
  KWStraightLineCycleOddTurning G embedding := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCycleOddTurning.of_cleanChordCompatibility hcompat embedding

/--
[kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cleanChordCompatibility](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPhaseClosure.lean)
-/
@[path]
private lemma kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cleanChordCompatibility_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hcompat : KWCleanChordPhaseCompatibility)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3) :
-- imply
  kwGraphFormalRoot G embedding.turnPhase = kwGraphFormalEvenPolynomial G := by
-- proof
  apply StatMech.FrontierA.kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cleanChordCompatibility hcompat G embedding hdeg

/--
[kacWard_straightLine_trivalent_of_cleanChordCompatibility](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPhaseClosure.lean)
-/
@[path]
private lemma kacWard_straightLine_trivalent_of_cleanChordCompatibility_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
-- given
  (hcompat : KWCleanChordPhaseCompatibility)
  (hdeg : ∀ vertex, G.degree vertex ≤ 3) :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_straightLine_trivalent_of_cleanChordCompatibility hcompat G embedding hdeg weight


-- created on 2026-10-23
