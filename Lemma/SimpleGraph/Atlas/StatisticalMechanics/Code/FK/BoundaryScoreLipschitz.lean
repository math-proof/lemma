import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.BoundaryScoreLipschitz
open StatMech StatMech.FK


/--
[openCount_add_diffSet_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryScoreLipschitz.lean)
-/
@[path]
private lemma openCount_add_diffSet_card_eq
  [Fintype V]
  [DecidableEq V]
  {omega eta : ConfigSpace (Sym2 V)} :
-- imply
  openCount G omega + (diffSet G omega eta).card = openCount G eta + (diffSet G eta omega).card := by
-- proof
  apply StatMech.FK.openCount_add_diffSet_card omega eta

/--
[numClustersBC_le_add_target_diffSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryScoreLipschitz.lean)
-/
@[path]
private lemma numClustersBC_le_add_target_diffSet_eq
  [Fintype V]
  [DecidableEq V]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {omega eta : ConfigSpace (Sym2 V)} :
-- imply
  numClustersBC G C omega <= numClustersBC G C eta + (diffSet G omega eta).card := by
-- proof
  apply StatMech.FK.numClustersBC_le_add_target_diffSet C omega eta

/--
[bcScore_le_add_configHammingCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryScoreLipschitz.lean)
-/
@[path]
private lemma bcScore_le_add_configHammingCount_eq
  [Fintype V]
  [DecidableEq V]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {omega eta : ConfigSpace (Sym2 V)} :
-- imply
  openCount G omega + 2 * numClustersBC G C omega <= openCount G eta + 2 * numClustersBC G C eta + configHammingCount G omega eta := by
-- proof
  apply StatMech.FK.bcScore_le_add_configHammingCount C omega eta

/--
[bcScore_le_add_configHammingCount_add_boundaryGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryScoreLipschitz.lean)
-/
@[path]
private lemma bcScore_le_add_configHammingCount_add_boundaryGap_eq
  [Fintype V]
  [DecidableEq V]
  {C D : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel D.Adj]
  {M : Nat}
  {omega eta : ConfigSpace (Sym2 V)}
-- given
  (hgap : numClustersBC G C eta <= numClustersBC G D eta + M) :
-- imply
  openCount G omega + 2 * numClustersBC G C omega <= openCount G eta + 2 * numClustersBC G D eta + configHammingCount G omega eta + 2 * M := by
-- proof
  apply StatMech.FK.bcScore_le_add_configHammingCount_add_boundaryGap C D M omega eta hgap


-- created on 2026-10-23
