import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqallclosed
open SimpleGraph Filter Topology Set StatMech StatMech.Walls


/--
[fkc_weight_allClosed_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqallclosed.lean)
-/
@[path]
private lemma fkc_weight_allClosed_ge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp1 : p < 1)
  (hq1 : 1 ≤ q) :
-- imply
  (1 - p) ^ G.edgeFinset.card ≤ fkWeight G p q (fkc_allClosed G).val := by
-- proof
  apply StatMech.Walls.fkc_weight_allClosed_ge G hp1 hq1

/--
[fkc_fkZEdge_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqallclosed.lean)
-/
@[path]
private lemma fkc_fkZEdge_ge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q) :
-- imply
  (1 - p) ^ G.edgeFinset.card ≤ ecz_fkZEdge G p q := by
-- proof
  apply StatMech.Walls.fkc_fkZEdge_ge G hp hp1 hq1

/--
[fkc_neglogZEdge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqallclosed.lean)
-/
@[path]
private lemma fkc_neglogZEdge_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q) :
-- imply
  -Real.log (ecz_fkZEdge G p q) ≤ (G.edgeFinset.card : ℝ) * (-Real.log (1 - p)) := by
-- proof
  apply StatMech.Walls.fkc_neglogZEdge_le G hp hp1 hq1

/--
[fkc_fkZEdge_ge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqallclosed.lean)
-/
@[path]
private lemma fkc_fkZEdge_ge_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q) :
-- imply
  fkc_fkZEdge_ge G hp hp1 hq1 = ecz_fkZEdge_ge_allClosed G hp hp1 hq1 := by
-- proof
  apply StatMech.Walls.fkc_fkZEdge_ge_eq G hp hp1 hq1

/--
[fkc_neglogZEdge_le_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqallclosed.lean)
-/
@[path]
private lemma fkc_neglogZEdge_le_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q) :
-- imply
  fkc_neglogZEdge_le G hp hp1 hq1 = ecz_neglogZEdge_le_edges G hp hp1 hq1 := by
-- proof
  apply StatMech.Walls.fkc_neglogZEdge_le_eq G hp hp1 hq1


-- created on 2026-10-23
