import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
open StatMech StatMech.FK


/--
[openSub_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean)
-/
@[path]
private lemma openSub_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)}
  {x y : V} :
-- imply
  (openSub G ω).Adj x y ↔ G.Adj x y ∧ ω s(x, y) = true := by
-- proof
  apply StatMech.FK.openSub_adj G ω x y

/--
[openSub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean)
-/
@[path]
private lemma openSub_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  openSub G ω ≤ G := by
-- proof
  apply StatMech.FK.openSub_le G ω

/--
[edgeProduct_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean)
-/
@[path]
private lemma edgeProduct_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 < edgeProduct G p ω := by
-- proof
  apply StatMech.FK.edgeProduct_pos G hp hp1 ω

/--
[fkWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean)
-/
@[path]
private lemma fkWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < fkWeight G p q ω := by
-- proof
  apply StatMech.FK.fkWeight_pos G hp hp1 hq ω

/--
[fkWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean)
-/
@[path]
private lemma fkWeight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ fkWeight G p q ω := by
-- proof
  apply StatMech.FK.fkWeight_nonneg G hp hp1 hq ω

/--
[fkZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean)
-/
@[path]
private lemma fkZ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < fkZ G p q := by
-- proof
  apply StatMech.FK.fkZ_pos G hp hp1 hq

/--
[fkZ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean)
-/
@[path]
private lemma fkZ_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkZ G p q ≠ 0 := by
-- proof
  apply StatMech.FK.fkZ_ne_zero G hp hp1 hq

/--
[fkProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean)
-/
@[path]
private lemma fkProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ fkProb G p q ω := by
-- proof
  apply StatMech.FK.fkProb_nonneg G hp hp1 hq ω

/--
[fkProb_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean)
-/
@[path]
private lemma fkProb_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < fkProb G p q ω := by
-- proof
  apply StatMech.FK.fkProb_pos G hp hp1 hq ω

/--
[fkProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean)
-/
@[path]
private lemma fkProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ ω : ConfigSpace (Sym2 V), fkProb G p q ω = 1 := by
-- proof
  apply StatMech.FK.fkProb_sum_eq_one G hp hp1 hq

/--
[fkPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean)
-/
@[path]
private lemma fkPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkPMF G hp hp1 hq ω = ENNReal.ofReal (fkProb G p q ω) := by
-- proof
  apply StatMech.FK.fkPMF_apply G hp hp1 hq ω

/--
[fkWeight_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean)
-/
@[path]
private lemma fkWeight_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  fkWeight G p 1 ω = edgeProduct G p ω := by
-- proof
  apply StatMech.FK.fkWeight_one G p ω

/--
[fkZ_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean)
-/
@[path]
private lemma fkZ_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ} :
-- imply
  fkZ G p 1 = ∑ ω : ConfigSpace (Sym2 V), edgeProduct G p ω := by
-- proof
  apply StatMech.FK.fkZ_one G p


-- created on 2026-10-23
