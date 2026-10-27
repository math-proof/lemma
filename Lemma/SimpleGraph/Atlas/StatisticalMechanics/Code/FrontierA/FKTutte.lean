import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FKTutte
open SimpleGraph StatMech StatMech.FK


/--
[edgeSetConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTutte.lean)
-/
@[path]
private lemma edgeSetConfig_apply_eq
  [Fintype V]
  [DecidableEq V]
  {A : Finset (Sym2 V)}
  {e : Sym2 V} :
-- imply
  edgeSetConfig A e = true ↔ e ∈ A := by
-- proof
  apply StatMech.FK.edgeSetConfig_apply A e

/--
[fkWeight_edgeSetConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTutte.lean)
-/
@[path]
private lemma fkWeight_edgeSetConfig_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset (Sym2 V)}
  {p q : ℝ}
-- given
  (hA : A ⊆ G.edgeFinset) :
-- imply
  fkWeight G p q (edgeSetConfig A) = p ^ A.card * (1 - p) ^ (G.edgeFinset.card - A.card) * q ^ spanningClusterCount A := by
-- proof
  apply StatMech.FK.fkWeight_edgeSetConfig G hA p q

/--
[randomClusterPartition_eq_sum_fkWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTutte.lean)
-/
@[path]
private lemma randomClusterPartition_eq_sum_fkWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ} :
-- imply
  randomClusterPartition G p q = ∑ A ∈ G.edgeFinset.powerset, fkWeight G p q (edgeSetConfig A) := by
-- proof
  apply StatMech.FK.randomClusterPartition_eq_sum_fkWeight G p q

/--
[randomClusterPartition_eq_tutte](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTutte.lean)
-/
@[path]
private lemma randomClusterPartition_eq_tutte_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  randomClusterPartition G p q = (1 - p) ^ G.edgeFinset.card * q ^ Nat.card G.ConnectedComponent * (p / (1 - p)) ^ (Fintype.card V - Nat.card G.ConnectedComponent) * tutteEval G (1 + q / (p / (1 - p))) (1 + p / (1 - p)) := by
-- proof
  apply StatMech.FK.randomClusterPartition_eq_tutte G hp hp1


-- created on 2026-10-23
