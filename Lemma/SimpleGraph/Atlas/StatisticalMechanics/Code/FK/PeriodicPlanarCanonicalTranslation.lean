import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation.Part4
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.shiftBufferedEquiv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma shiftBufferedEquiv_val_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {n : Nat}
  {x : P.BufferedVertex n} :
-- imply
  (P.shiftBufferedEquiv z n x : V) = P.shift z x.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shiftBufferedEquiv_val P z n x

/--
[PeriodicGraph.shiftBufferedEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma shiftBufferedEquiv_adj_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {n : Nat}
  {x y : P.BufferedVertex n} :
-- imply
  (P.bufferedGraph n).Adj x y ↔ (P.shiftedBufferedGraph z n).Adj (P.shiftBufferedEquiv z n x) (P.shiftBufferedEquiv z n y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shiftBufferedEquiv_adj P z n x y

/--
[PeriodicGraph.shift_orbitBox_subset_orbitBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma shift_orbitBox_subset_orbitBox_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {n : Nat} :
-- imply
  P.shift z '' (P.orbitBox n : Set V) ⊆ (P.orbitBox (n + flc_vrad z) : Set V) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shift_orbitBox_subset_orbitBox P z n

/--
[PeriodicGraph.orbitBox_subset_shift_orbitBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma orbitBox_subset_shift_orbitBox_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {a n : Nat}
-- given
  (h : a + flc_vrad z ≤ n) :
-- imply
  (P.orbitBox a : Set V) ⊆ P.shift z '' (P.orbitBox n : Set V) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.orbitBox_subset_shift_orbitBox P z h

/--
[PeriodicGraph.bufferedRadius_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma bufferedRadius_add_le_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {n c : Nat} :
-- imply
  P.bufferedRadius n + c ≤ P.bufferedRadius (n + c) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRadius_add_le P n c

/--
[PeriodicGraph.shiftedBuffered_subset_buffered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma shiftedBuffered_subset_buffered_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {n : Nat} :
-- imply
  (P.shiftedBufferedVertices z n : Set V) ⊆ (P.orbitBox (P.bufferedRadius (n + flc_vrad z)) : Set V) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shiftedBuffered_subset_buffered P z n

/--
[PeriodicGraph.buffered_subset_shiftedBuffered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma buffered_subset_shiftedBuffered_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {a n : Nat}
-- given
  (h : a + flc_vrad z ≤ n) :
-- imply
  (P.orbitBox (P.bufferedRadius a) : Set V) ⊆ (P.shiftedBufferedVertices z n : Set V) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.buffered_subset_shiftedBuffered P z h

/--
[PeriodicGraph.freeBufferedMeasure_real_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma freeBufferedMeasure_real_multiOpen_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {n : Nat}
  {p q : Real}
  {t : Finset (Sym2 (P.BufferedVertex n))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (P.freeBufferedMeasure n hp hp1 hq : Measure (ConfigSpace (Sym2 V))).real (fmu_multiOpen (t.image (P.edgeIncl (P.bufferedRadius n)))) = med_multiMassProb (fkProb (P.bufferedGraph n) p q) t := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedMeasure_real_multiOpen P n hp hp1 hq t

/--
[PeriodicGraph.centered_eq_shifted_free_multiMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma centered_eq_shifted_free_multiMass_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {n : Nat}
  {t : Finset (Sym2 (P.BufferedVertex n))}
  {p q : Real} :
-- imply
  med_multiMassProb (fkProb (P.bufferedGraph n) p q) t = med_multiMassProb (fkProb (P.shiftedBufferedGraph z n) p q) (t.image (Sym2.map (P.shiftBufferedEquiv z n))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.centered_eq_shifted_free_multiMass P z n t p q

/--
[PeriodicGraph.shifted_free_multiMass_le_buffered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma shifted_free_multiMass_le_buffered_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {n m : Nat}
  {p q : Real}
  {t : Finset (Sym2 (P.ShiftedBufferedVertex z n))}
-- given
  (hsub : (P.shiftedBufferedVertices z n : Set V) ⊆ (P.orbitBox (P.bufferedRadius m) : Set V))
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  med_multiMassProb (fkProb (P.shiftedBufferedGraph z n) p q) t ≤ med_multiMassProb (fkProb (P.bufferedGraph m) p q) (t.image (ocd_innerEdge (P.shiftedToBufferedIncl z n m hsub))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shifted_free_multiMass_le_buffered P z n m hsub hp hp1 hq t

/--
[PeriodicGraph.buffered_free_multiMass_le_shifted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma buffered_free_multiMass_le_shifted_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {n m : Nat}
  {p q : Real}
  {t : Finset (Sym2 (P.BufferedVertex n))}
-- given
  (hsub : (P.orbitBox (P.bufferedRadius n) : Set V) ⊆ (P.shiftedBufferedVertices z m : Set V))
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  med_multiMassProb (fkProb (P.bufferedGraph n) p q) t ≤ med_multiMassProb (fkProb (P.shiftedBufferedGraph z m) p q) (t.image (ocd_innerEdge (P.bufferedToShiftedIncl z n m hsub))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.buffered_free_multiMass_le_shifted P z n m hsub hp hp1 hq t

/--
[PeriodicGraph.shiftedFreeMultiMass_eq_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma shiftedFreeMultiMass_eq_centered_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {N : Nat}
  {t : Finset (Sym2 (P.BufferedVertex N))}
  {p q : Real}
  {m : Nat}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hNm : N ≤ m) :
-- imply
  P.shiftedFreeMultiMass z N t p q m hNm = (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (fmu_multiOpen (t.image (P.edgeIncl (P.bufferedRadius N)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shiftedFreeMultiMass_eq_centered P z N t hp hp1 hq m hNm

/--
[PeriodicGraph.shiftedFreeMultiMass_le_centered_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma shiftedFreeMultiMass_le_centered_shift_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {N : Nat}
  {t : Finset (Sym2 (P.BufferedVertex N))}
  {p q : Real}
  {m : Nat}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hNm : N ≤ m) :
-- imply
  P.shiftedFreeMultiMass z N t p q m hNm ≤ (P.freeBufferedMeasure (m + flc_vrad z) hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (fmu_multiOpen ((t.image (P.edgeIncl (P.bufferedRadius N))).image (Sym2.map (P.shift z)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shiftedFreeMultiMass_le_centered_shift P z N t hp hp1 hq m hNm

/--
[PeriodicGraph.centered_shift_le_shiftedFreeMultiMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma centered_shift_le_shiftedFreeMultiMass_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {N : Nat}
  {t : Finset (Sym2 (P.BufferedVertex N))}
  {p q : Real}
  {m a : Nat}
  {ta : Finset (Sym2 (P.BufferedVertex a))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hNm : N ≤ m)
  (ha : a + flc_vrad z ≤ m)
  (hta : ta.image (P.edgeIncl (P.bufferedRadius a)) = (t.image (P.edgeIncl (P.bufferedRadius N))).image (Sym2.map (P.shift z))) :
-- imply
  (P.freeBufferedMeasure a hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (fmu_multiOpen ((t.image (P.edgeIncl (P.bufferedRadius N))).image (Sym2.map (P.shift z)))) ≤ P.shiftedFreeMultiMass z N t p q m hNm := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.centered_shift_le_shiftedFreeMultiMass P z N t hp hp1 hq m a hNm ha ta hta

/--
[isClopen_fmu_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma isClopen_fmu_multiOpen_eq
  [DecidableEq V]
  [Countable V]
  {T : Finset (Sym2 V)} :
-- imply
  IsClopen (fmu_multiOpen T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.isClopen_fmu_multiOpen T

/--
[PeriodicGraph.bufferedEdgeLift_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma bufferedEdgeLift_image_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N : Nat}
  {T : Finset (Sym2 V)}
-- given
  (hT : ∀ e ∈ T, e ∈ Set.range (P.edgeIncl (P.bufferedRadius N))) :
-- imply
  (P.bufferedEdgeLift N T hT).image (P.edgeIncl (P.bufferedRadius N)) = T := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedEdgeLift_image P N T hT

/--
[PeriodicGraph.shiftedFreeMultiMass_tendsto_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma shiftedFreeMultiMass_tendsto_centered_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {N : Nat}
  {t : Finset (Sym2 (P.BufferedVertex N))}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun k => P.shiftedFreeMultiMass z N t p q (N + k) (Nat.le_add_right N k)) atTop (nhds ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (fmu_multiOpen (t.image (P.edgeIncl (P.bufferedRadius N)))))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shiftedFreeMultiMass_tendsto_centered P z N t hp hp1 hq

/--
[PeriodicGraph.shiftedFreeMultiMass_tendsto_shifted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma shiftedFreeMultiMass_tendsto_shifted_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {N : Nat}
  {t : Finset (Sym2 (P.BufferedVertex N))}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun k => P.shiftedFreeMultiMass z N t p q (N + k) (Nat.le_add_right N k)) atTop (nhds ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (fmu_multiOpen ((t.image (P.edgeIncl (P.bufferedRadius N))).image (Sym2.map (P.shift z)))))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shiftedFreeMultiMass_tendsto_shifted P z N t hp hp1 hq

/--
[PeriodicGraph.freeBufferedInfiniteVolume_multiOpen_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_multiOpen_shift_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {T : Finset (Sym2 V)}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) (fmu_multiOpen T) = (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) (fmu_multiOpen (T.image (Sym2.map (P.shift z)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_multiOpen_shift P z T hp hp1 hq

/--
[PeriodicGraph.configTranslate_preimage_fmu_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma configTranslate_preimage_fmu_multiOpen_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {T : Finset (Sym2 V)} :
-- imply
  P.configTranslate z ⁻¹' fmu_multiOpen T = fmu_multiOpen (T.image (Sym2.map (P.shift (-z)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.configTranslate_preimage_fmu_multiOpen P z T

/--
[PeriodicGraph.freeBufferedInfiniteVolume_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_isTranslationInvariant_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  P.IsTranslationInvariant (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_isTranslationInvariant P hp hp1 hq


-- created on 2026-10-23
