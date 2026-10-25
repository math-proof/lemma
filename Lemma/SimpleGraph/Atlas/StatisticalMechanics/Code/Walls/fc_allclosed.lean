import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.fc_allclosed
open SimpleGraph Filter Topology Set StatMech StatMech.Walls


/--
[fc_weight_allClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_allclosed.lean)
-/
@[path]
private lemma fc_weight_allClosed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ} :
-- imply
  fkWeight G p q (fc_allClosed G).val = (1 - p) ^ G.edgeFinset.card * q ^ FK.numClusters G (fun _ => false) := by
-- proof
  apply StatMech.Walls.fc_weight_allClosed G p q

/--
[fc_weight_allClosed_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_allclosed.lean)
-/
@[path]
private lemma fc_weight_allClosed_ge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp1 : p < 1)
  (hq1 : 1 ≤ q) :
-- imply
  (1 - p) ^ G.edgeFinset.card ≤ fkWeight G p q (fc_allClosed G).val := by
-- proof
  apply StatMech.Walls.fc_weight_allClosed_ge G hp1 hq1

/--
[fc_fkZEdge_ge_allClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_allclosed.lean)
-/
@[path]
private lemma fc_fkZEdge_ge_allClosed_eq
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
  apply StatMech.Walls.fc_fkZEdge_ge_allClosed G hp hp1 hq1

/--
[fc_neglogZEdge_le_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_allclosed.lean)
-/
@[path]
private lemma fc_neglogZEdge_le_edges_eq
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
  apply StatMech.Walls.fc_neglogZEdge_le_edges G hp hp1 hq1

/--
[fc_neglogZEdge_le_edges'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_allclosed.lean)
-/
@[path]
private lemma fc_neglogZEdge_le_edges'_eq
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
  apply StatMech.Walls.fc_neglogZEdge_le_edges' G hp hp1 hq1

/--
[fc_fkZEdge_ge_allClosed_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_allclosed.lean)
-/
@[path]
private lemma fc_fkZEdge_ge_allClosed_eq_eq
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
  fc_fkZEdge_ge_allClosed G hp hp1 hq1 = ecz_fkZEdge_ge_allClosed G hp hp1 hq1 := by
-- proof
  apply StatMech.Walls.fc_fkZEdge_ge_allClosed_eq G hp hp1 hq1

/--
[fc_neglogZEdge_le_edges_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_allclosed.lean)
-/
@[path]
private lemma fc_neglogZEdge_le_edges_eq_eq
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
  fc_neglogZEdge_le_edges G hp hp1 hq1 = ecz_neglogZEdge_le_edges G hp hp1 hq1 := by
-- proof
  apply StatMech.Walls.fc_neglogZEdge_le_edges_eq G hp hp1 hq1


-- created on 2026-10-23
