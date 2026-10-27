import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.fc_weightle
open SimpleGraph StatMech StatMech.Walls StatMech.Walls.FK


/--
[fc_edgeProduct_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_weightle.lean)
-/
@[path]
private lemma fc_edgeProduct_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ edgeProduct G p ω := by
-- proof
  apply StatMech.Walls.FK.fc_edgeProduct_nonneg G hp hp1 ω

/--
[fc_edgeProduct_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_weightle.lean)
-/
@[path]
private lemma fc_edgeProduct_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  edgeProduct G p ω ≤ 1 := by
-- proof
  apply StatMech.Walls.FK.fc_edgeProduct_le_one G hp hp1 ω

/--
[fc_qpow_numClusters_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_weightle.lean)
-/
@[path]
private lemma fc_qpow_numClusters_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hq : 1 ≤ q) :
-- imply
  q ^ numClusters G ω ≤ q ^ Fintype.card V := by
-- proof
  apply StatMech.Walls.FK.fc_qpow_numClusters_le G hq ω

/--
[fc_fkWeight_le_qpow_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_weightle.lean)
-/
@[path]
private lemma fc_fkWeight_le_qpow_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hq : 1 ≤ q) :
-- imply
  fkWeight G p q ω ≤ q ^ Fintype.card V := by
-- proof
  apply StatMech.Walls.FK.fc_fkWeight_le_qpow_card G hp hp1 hq ω

/--
[fc_fkWeight_le_qpow_card'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_weightle.lean)
-/
@[path]
private lemma fc_fkWeight_le_qpow_card'_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hq : 1 ≤ q) :
-- imply
  fkWeight G p q ω ≤ q ^ (Finset.univ : Finset V).card := by
-- proof
  apply StatMech.Walls.FK.fc_fkWeight_le_qpow_card' G hp hp1 hq ω


-- created on 2026-10-23
