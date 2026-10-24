import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.FiniteMomentsFull
open MeasureTheory StatMech StatMech.BeffaraDC


/--
[fkCluster_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma fkCluster_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace (Sym2 V)}
  {x : V}
-- given
  (hab : a ≤ b) :
-- imply
  fkCluster G a x ⊆ fkCluster G b x := by
-- proof
  apply StatMech.BeffaraDC.fkCluster_mono G hab x

/--
[fkClusterSizeLargeEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma fkClusterSizeLargeEvent_isIncreasing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {N : ℕ} :
-- imply
  IsIncreasing (fkClusterSizeLargeEvent G x N) := by
-- proof
  apply StatMech.BeffaraDC.fkClusterSizeLargeEvent_isIncreasing G x N

/--
[measurableSet_fkClusterSizeLargeEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma measurableSet_fkClusterSizeLargeEvent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {N : ℕ} :
-- imply
  MeasurableSet (fkClusterSizeLargeEvent G x N) := by
-- proof
  apply StatMech.BeffaraDC.measurableSet_fkClusterSizeLargeEvent G x N

/--
[fkClusterSizeTail_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma fkClusterSizeTail_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x : V}
  {N : ℕ} :
-- imply
  0 ≤ fkClusterSizeTail G p q x N := by
-- proof
  apply StatMech.BeffaraDC.fkClusterSizeTail_nonneg G p q x N

/--
[fkClusterSizeLargeEvent_eq_empty_of_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma fkClusterSizeLargeEvent_eq_empty_of_card_lt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
  {N : ℕ}
-- given
  (hN : Fintype.card V < N) :
-- imply
  fkClusterSizeLargeEvent G x N = ∅ := by
-- proof
  apply StatMech.BeffaraDC.fkClusterSizeLargeEvent_eq_empty_of_card_lt G x hN

/--
[fkClusterSizeTail_eq_zero_of_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma fkClusterSizeTail_eq_zero_of_card_lt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x : V}
  {N : ℕ}
-- given
  (hN : Fintype.card V < N) :
-- imply
  fkClusterSizeTail G p q x N = 0 := by
-- proof
  apply StatMech.BeffaraDC.fkClusterSizeTail_eq_zero_of_card_lt G p q x hN

/--
[fkClusterSizeTail_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma fkClusterSizeTail_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x : V}
  {N : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkClusterSizeTail G p q x N ≤ 1 := by
-- proof
  apply StatMech.BeffaraDC.fkClusterSizeTail_le_one G hp hp1 hq x N

/--
[fkClusterSizeTail_le_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma fkClusterSizeTail_le_bernoulli_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x : V}
  {N : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  fkClusterSizeTail G p q x N ≤ fkClusterSizeTail G p 1 x N := by
-- proof
  apply StatMech.BeffaraDC.fkClusterSizeTail_le_bernoulli G hp hp1 hq x N

/--
[fkClusterSizeTail_geometricTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma fkClusterSizeTail_geometricTail_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x : V}
  {C r : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) :
-- imply
  ∀ N, fkClusterSizeTail G p q x N ≤ C * r ^ N := by
-- proof
  apply StatMech.BeffaraDC.fkClusterSizeTail_geometricTail G hp hp1 hq x hbtail

/--
[exists_geometricTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma exists_geometricTail_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x : V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∃ C r, 0 ≤ r ∧ r < 1 ∧ ∀ N, fkClusterSizeTail G p q x N ≤ C * r ^ N := by
-- proof
  apply StatMech.BeffaraDC.exists_geometricTail G hp hp1 hq x

/--
[fkClusterSizeDomination_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma fkClusterSizeDomination_dist_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x : V}
  {C r : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hr0 : 0 ≤ r)
  (hr1 : r < 1)
  (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) :
-- imply
  (fkClusterSizeDomination G hp hp1 hq x hr0 hr1 hbtail).dist = fun N => fkClusterSizeTail G p q x N := by
-- proof
  apply StatMech.BeffaraDC.fkClusterSizeDomination_dist G hp hp1 hq x hr0 hr1 hbtail

/--
[fkClusterSizeMoment_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma fkClusterSizeMoment_lt_top_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x : V}
  {C r : ℝ}
  {d : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hr0 : 0 ≤ r)
  (hr1 : r < 1)
  (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) :
-- imply
  clusterMoment (fun N => fkClusterSizeTail G p q x N) d ≤ ∑' N : ℕ, (N : ℝ) ^ d * (C * r ^ N) := by
-- proof
  apply StatMech.BeffaraDC.fkClusterSizeMoment_lt_top G hp hp1 hq x hr0 hr1 hbtail d

/--
[fkClusterSizeMoment_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma fkClusterSizeMoment_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {x : V}
  {d : ℕ} :
-- imply
  0 ≤ clusterMoment (fun N => fkClusterSizeTail G p q x N) d := by
-- proof
  apply StatMech.BeffaraDC.fkClusterSizeMoment_nonneg G p q x d

/--
[bernoulliClusterSizeMoment_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean)
-/
@[path]
private lemma bernoulliClusterSizeMoment_lt_top_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {x : V}
  {C r : ℝ}
  {d : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hr0 : 0 ≤ r)
  (hr1 : r < 1)
  (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) :
-- imply
  clusterMoment (fun N => fkClusterSizeTail G p 1 x N) d ≤ ∑' N : ℕ, (N : ℝ) ^ d * (C * r ^ N) := by
-- proof
  apply StatMech.BeffaraDC.bernoulliClusterSizeMoment_lt_top G hp hp1 x hr0 hr1 hbtail d


-- created on 2026-10-23
