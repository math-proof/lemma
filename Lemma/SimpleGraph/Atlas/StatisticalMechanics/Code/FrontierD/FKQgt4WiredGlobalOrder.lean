import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4WiredGlobalOrder
open MeasureTheory Set SimpleGraph StatMech StatMech.FrontierD


/--
[numInfiniteClusters_eq_one_subset_hasInfiniteClusterEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredGlobalOrder.lean)
-/
@[path]
private lemma numInfiniteClusters_eq_one_subset_hasInfiniteClusterEvent_eq
  {d : Nat} :
-- imply
  {omega | numInfiniteClusters d omega = 1} ⊆ hasInfiniteClusterEvent d := by
-- proof
  apply StatMech.FrontierD.numInfiniteClusters_eq_one_subset_hasInfiniteClusterEvent d

/--
[wiredInfiniteVolume_hasInfiniteClusterEvent_eq_one_of_percolation_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredGlobalOrder.lean)
-/
@[path]
private lemma wiredInfiniteVolume_hasInfiniteClusterEvent_eq_one_of_percolation_pos_eq
  {d : Nat}
  {p q : Real}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (htheta : 0 < ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d)) :
-- imply
  ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))) (hasInfiniteClusterEvent d) = 1 := by
-- proof
  apply StatMech.FrontierD.wiredInfiniteVolume_hasInfiniteClusterEvent_eq_one_of_percolation_pos hd hp hp1 hq htheta

/--
[wiredInfiniteVolume_hasInfiniteClusterEvent_eq_one_iff_percolation_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredGlobalOrder.lean)
-/
@[path]
private lemma wiredInfiniteVolume_hasInfiniteClusterEvent_eq_one_iff_percolation_pos_eq
  {d : Nat}
  {p q : Real}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))) (hasInfiniteClusterEvent d) = 1 ↔ 0 < ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d) := by
-- proof
  apply StatMech.FrontierD.wiredInfiniteVolume_hasInfiniteClusterEvent_eq_one_iff_percolation_pos hd hp hp1 hq


-- created on 2026-10-23
