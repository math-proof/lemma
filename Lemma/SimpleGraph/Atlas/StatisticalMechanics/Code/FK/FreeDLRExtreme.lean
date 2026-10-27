import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FreeDLRExtreme
open MeasureTheory Set Topology StatMech StatMech.FK


/--
[exactFiniteCylinder_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRExtreme.lean)
-/
@[path]
private lemma exactFiniteCylinder_isOpen_eq
  {F : Finset E}
  {omega : ConfigSpace E} :
-- imply
  IsOpen (exactFiniteCylinder F omega) := by
-- proof
  apply StatMech.FK.exactFiniteCylinder_isOpen F omega

/--
[isClopen_dependsOn_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRExtreme.lean)
-/
@[path]
private lemma isClopen_dependsOn_finset_eq
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsClopen A) :
-- imply
  ∃ F : Finset E, StatMech.DependsOn A (F : Set E) := by
-- proof
  apply StatMech.FK.isClopen_dependsOn_finset A hA

/--
[isClopen_eq_boxRestrict_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRExtreme.lean)
-/
@[path]
private lemma isClopen_eq_boxRestrict_preimage_eq
  {d : ℕ}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hA : IsClopen A) :
-- imply
  ∃ (N : ℕ) (S : Set (ConfigSpace (Sym2 (boxVerts d N)))), A = boxRestrict d N ⁻¹' S ∧ (IsIncreasing A → IsIncreasing S) := by
-- proof
  apply StatMech.FK.isClopen_eq_boxRestrict_preimage A hA

/--
[freeInfiniteVolume_le_isFKDLR_clopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRExtreme.lean)
-/
@[path]
private lemma freeInfiniteVolume_le_isFKDLR_clopen_eq
  {d : ℕ}
  {p q : ℝ}
  {phi : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hphi : IsFKDLR d p q phi) :
-- imply
  Ising.StochasticallyDominatedClopen (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) (phi : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_le_isFKDLR_clopen hp hp1 hq phi hphi

/--
[freeInfiniteVolume_weakDLR_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRExtreme.lean)
-/
@[path]
private lemma freeInfiniteVolume_weakDLR_extreme_eq
  {d : ℕ}
  {p q : ℝ}
  {phi1 phi2 : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hphi1 : IsFKDLR d p q phi1)
  (hphi2 : IsFKDLR d p q phi2)
  (a b : ℝ≥0∞)
  (ha : 0 < a)
  (hb : 0 < b)
  (hab : a + b = 1)
  (hconv : (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) = a • (phi1 : Measure (ConfigSpace (Sym2 (Site d)))) + b • (phi2 : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  (phi1 : Measure (ConfigSpace (Sym2 (Site d)))) = (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) ∧ (phi2 : Measure (ConfigSpace (Sym2 (Site d)))) = (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_weakDLR_extreme hp hp1 hq phi1 phi2 hphi1 hphi2 a b ha hb hab hconv

/--
[freeInfinite_canonical_uniqueness_of_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRExtreme.lean)
-/
@[path]
private lemma freeInfinite_canonical_uniqueness_of_isErgodic_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (herg : StatMech.ConfigSpace.IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters d omega = 0} = 1 ∨ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters d omega = 1} = 1) ∧ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) (atLeastTwoInfinite d) = 0 ∧ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FK.freeInfinite_canonical_uniqueness_of_isErgodic hd hp hp1 hq herg

/--
[freeInfinite_q2_canonical_uniqueness_of_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRExtreme.lean)
-/
@[path]
private lemma freeInfinite_q2_canonical_uniqueness_of_isErgodic_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (herg : StatMech.ConfigSpace.IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  ((freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | numInfiniteClusters d omega = 0} = 1 ∨ (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | numInfiniteClusters d omega = 1} = 1) ∧ (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) (atLeastTwoInfinite d) = 0 ∧ (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FK.freeInfinite_q2_canonical_uniqueness_of_isErgodic hd hp hp1 herg


-- created on 2026-10-23
