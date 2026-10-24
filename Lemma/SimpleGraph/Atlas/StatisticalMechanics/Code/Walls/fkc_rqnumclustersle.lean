import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.fkc_rqnumclustersle
open SimpleGraph StatMech StatMech.Walls StatMech.Walls.FK


/--
[fkc_card_connectedComponent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqnumclustersle.lean)
-/
@[path]
private lemma fkc_card_connectedComponent_le_eq
  [Fintype V]
  {G : SimpleGraph V}
  [Fintype G.ConnectedComponent] :
-- imply
  Fintype.card G.ConnectedComponent ≤ Fintype.card V := by
-- proof
  apply StatMech.Walls.fkc_card_connectedComponent_le G

/--
[fkc_numClusters_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqnumclustersle.lean)
-/
@[path]
private lemma fkc_numClusters_le_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  numClusters G ω ≤ Fintype.card V := by
-- proof
  apply StatMech.Walls.FK.fkc_numClusters_le_card G ω

/--
[fkc_numClusters_le_card'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqnumclustersle.lean)
-/
@[path]
private lemma fkc_numClusters_le_card'_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  numClusters G ω ≤ (Finset.univ : Finset V).card := by
-- proof
  apply StatMech.Walls.FK.fkc_numClusters_le_card' G ω


-- created on 2026-10-23
