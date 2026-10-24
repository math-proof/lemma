import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TrifurcationPatternCapstone
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.FK


/--
[wiredInfinite_trifurcation_pos_of_top_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TrifurcationPatternCapstone.lean)
-/
@[path]
private lemma wiredInfinite_trifurcation_pos_of_top_pos_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (htop : 0 < (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters d omega = ⊤}) :
-- imply
  0 < (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | IsTrifurcation d omega 0} := by
-- proof
  apply StatMech.FK.wiredInfinite_trifurcation_pos_of_top_pos hp hp1 hq htop

/--
[freeInfinite_trifurcation_pos_of_top_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TrifurcationPatternCapstone.lean)
-/
@[path]
private lemma freeInfinite_trifurcation_pos_of_top_pos_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (htop : 0 < (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters d omega = ⊤}) :
-- imply
  0 < (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | IsTrifurcation d omega 0} := by
-- proof
  apply StatMech.FK.freeInfinite_trifurcation_pos_of_top_pos hp hp1 hq htop

/--
[wiredInfinite_canonical_trifurcation_pos_of_top_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TrifurcationPatternCapstone.lean)
-/
@[path]
private lemma wiredInfinite_canonical_trifurcation_pos_of_top_pos_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (htop : 0 < (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters d omega = ⊤}) :
-- imply
  0 < (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | IsCanonicalTrifurcation d omega 0} := by
-- proof
  apply StatMech.FK.wiredInfinite_canonical_trifurcation_pos_of_top_pos hp hp1 hq htop

/--
[freeInfinite_canonical_trifurcation_pos_of_top_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TrifurcationPatternCapstone.lean)
-/
@[path]
private lemma freeInfinite_canonical_trifurcation_pos_of_top_pos_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (htop : 0 < (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters d omega = ⊤}) :
-- imply
  0 < (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | IsCanonicalTrifurcation d omega 0} := by
-- proof
  apply StatMech.FK.freeInfinite_canonical_trifurcation_pos_of_top_pos hp hp1 hq htop

/--
[wiredInfinite_q2_trifurcation_pos_of_top_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TrifurcationPatternCapstone.lean)
-/
@[path]
private lemma wiredInfinite_q2_trifurcation_pos_of_top_pos_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (htop : 0 < (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | numInfiniteClusters d omega = ⊤}) :
-- imply
  0 < (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | IsTrifurcation d omega 0} := by
-- proof
  apply StatMech.FK.wiredInfinite_q2_trifurcation_pos_of_top_pos hp hp1 htop

/--
[freeInfinite_q2_trifurcation_pos_of_top_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TrifurcationPatternCapstone.lean)
-/
@[path]
private lemma freeInfinite_q2_trifurcation_pos_of_top_pos_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (htop : 0 < (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | numInfiniteClusters d omega = ⊤}) :
-- imply
  0 < (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | IsTrifurcation d omega 0} := by
-- proof
  apply StatMech.FK.freeInfinite_q2_trifurcation_pos_of_top_pos hp hp1 htop

/--
[wiredInfinite_q2_canonical_trifurcation_pos_of_top_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TrifurcationPatternCapstone.lean)
-/
@[path]
private lemma wiredInfinite_q2_canonical_trifurcation_pos_of_top_pos_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (htop : 0 < (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | numInfiniteClusters d omega = ⊤}) :
-- imply
  0 < (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | IsCanonicalTrifurcation d omega 0} := by
-- proof
  apply StatMech.FK.wiredInfinite_q2_canonical_trifurcation_pos_of_top_pos hp hp1 htop

/--
[freeInfinite_q2_canonical_trifurcation_pos_of_top_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TrifurcationPatternCapstone.lean)
-/
@[path]
private lemma freeInfinite_q2_canonical_trifurcation_pos_of_top_pos_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (htop : 0 < (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | numInfiniteClusters d omega = ⊤}) :
-- imply
  0 < (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | IsCanonicalTrifurcation d omega 0} := by
-- proof
  apply StatMech.FK.freeInfinite_q2_canonical_trifurcation_pos_of_top_pos hp hp1 htop

/--
[wiredInfinite_q2_canonical_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TrifurcationPatternCapstone.lean)
-/
@[path]
private lemma wiredInfinite_q2_canonical_uniqueness_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ((wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | numInfiniteClusters d omega = 0} = 1 ∨ (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | numInfiniteClusters d omega = 1} = 1) ∧ (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) (atLeastTwoInfinite d) = 0 ∧ (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FK.wiredInfinite_q2_canonical_uniqueness hd hp hp1


-- created on 2026-10-23
