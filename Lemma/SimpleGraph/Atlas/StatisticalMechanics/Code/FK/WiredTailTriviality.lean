import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.WiredTailTriviality
open MeasureTheory ProbabilityTheory Set Filter Topology StatMech StatMech.FK


/--
[wiredFinite_inter_outside_le_mul_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredTailTriviality.lean)
-/
@[path]
private lemma wiredFinite_inter_outside_le_mul_generalQ_eq
  {d : Nat}
  {N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
  {B : Set (ConfigSpace (Sym2 (boxVerts d m)))}
-- given
  (hN : 1 <= N)
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A)
  (hB : DependsOnOutside (ocd_innerEdgeFinset (Vin := boxVerts d N) (boxVertInclLE d (le_of_lt hNm))) B) :
-- imply
  (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d m ⁻¹' ((ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) ⁻¹' A) ∩ B)) <= (wiredFiniteMeasure d N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) * (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d m ⁻¹' B) := by
-- proof
  apply StatMech.FK.wiredFinite_inter_outside_le_mul_generalQ hN hNm hp hp1 hq hA hB

/--
[wiredInfiniteVolume_inter_boxOutside_le_finite_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredTailTriviality.lean)
-/
@[path]
private lemma wiredInfiniteVolume_inter_boxOutside_le_finite_generalQ_eq
  {d : Nat}
  {N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
  {B : Set (ConfigSpace (Sym2 (boxVerts d m)))}
-- given
  (hN : 1 <= N)
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A)
  (hB : DependsOnOutside (ocd_innerEdgeFinset (Vin := boxVerts d N) (boxVertInclLE d (le_of_lt hNm))) B) :
-- imply
  (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real ((boxRestrict d N ⁻¹' A) ∩ (boxRestrict d m ⁻¹' B)) <= (wiredFiniteMeasure d N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) * (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d m ⁻¹' B) := by
-- proof
  apply StatMech.FK.wiredInfiniteVolume_inter_boxOutside_le_finite_generalQ hN hNm hp hp1 hq hA hB

/--
[wiredInfiniteVolume_inter_exterior_le_finite_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredTailTriviality.lean)
-/
@[path]
private lemma wiredInfiniteVolume_inter_exterior_le_finite_generalQ_eq
  {d : Nat}
  {N : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
  {s : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hN : 1 <= N)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A)
  (hs : @MeasurableSet _ (outsideSigma (fkTailEdgeWindow d N)) s) :
-- imply
  (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real ((boxRestrict d N ⁻¹' A) ∩ s) <= (wiredFiniteMeasure d N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) * (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real s := by
-- proof
  apply StatMech.FK.wiredInfiniteVolume_inter_exterior_le_finite_generalQ N hN hp hp1 hq hA hs

/--
[wiredInfiniteVolume_tail_box_inter_le_mul_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredTailTriviality.lean)
-/
@[path]
private lemma wiredInfiniteVolume_tail_box_inter_le_mul_generalQ_eq
  {d : Nat}
  {p q : Real}
  {s : Set (ConfigSpace (Sym2 (Site d)))}
  {R : Nat}
  {A : Set (ConfigSpace (Sym2 (boxVerts d R)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hs : FKIsTailEvent d s)
  (hA : IsIncreasing A) :
-- imply
  (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real ((boxRestrict d R ⁻¹' A) ∩ s) <= (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d R ⁻¹' A) * (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real s := by
-- proof
  apply StatMech.FK.wiredInfiniteVolume_tail_box_inter_le_mul_generalQ hp hp1 hq s hs R hA

/--
[cond_tail_le_wiredInfiniteVolume_clopen_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredTailTriviality.lean)
-/
@[path]
private lemma cond_tail_le_wiredInfiniteVolume_clopen_generalQ_eq
  {d : Nat}
  {p q : Real}
  {s : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hs : FKIsTailEvent d s)
  (hs0 : (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) s ≠ 0) :
-- imply
  Ising.StochasticallyDominatedClopen (((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _))[|s]) (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.cond_tail_le_wiredInfiniteVolume_clopen_generalQ hp hp1 hq hs hs0

/--
[wiredInfiniteVolume_tail_trivial_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredTailTriviality.lean)
-/
@[path]
private lemma wiredInfiniteVolume_tail_trivial_generalQ_eq
  {d : Nat}
  {p q : Real}
  {s : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hs : FKIsTailEvent d s) :
-- imply
  (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) s = 0 ∨ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) s = 1 := by
-- proof
  apply StatMech.FK.wiredInfiniteVolume_tail_trivial_generalQ hp hp1 hq s hs

/--
[wiredInfiniteVolume_isErgodic_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredTailTriviality.lean)
-/
@[path]
private lemma wiredInfiniteVolume_isErgodic_generalQ_eq
  {d : Nat}
  {p q : Real}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  StatMech.ConfigSpace.IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.wiredInfiniteVolume_isErgodic_generalQ hd hp hp1 hq

/--
[wiredInfinite_canonical_uniqueness_all_parameters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredTailTriviality.lean)
-/
@[path]
private lemma wiredInfinite_canonical_uniqueness_all_parameters_eq
  {d : Nat}
  {p q : Real}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | Percolation.numInfiniteClusters d omega = 0} = 1 ∨ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | Percolation.numInfiniteClusters d omega = 1} = 1) ∧ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) (Percolation.atLeastTwoInfinite d) = 0 ∧ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | Percolation.numInfiniteClusters d omega <= 1} = 1 := by
-- proof
  apply StatMech.FK.wiredInfinite_canonical_uniqueness_all_parameters hd hp hp1 hq


-- created on 2026-10-23
