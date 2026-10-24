import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFiniteEnergy
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.bufferedRestrictLE_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma bufferedRestrictLE_setOpen_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N m : Nat}
  {e : Sym2 (P.BufferedVertex N)}
  {omega : ConfigSpace (Sym2 (P.BufferedVertex m))}
-- given
  (hNm : N <= m) :
-- imply
  P.bufferedRestrictLE hNm (setOpen (Sym2.map (P.bufferedVertexInclLE hNm) e) omega) = setOpen e (P.bufferedRestrictLE hNm omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRestrictLE_setOpen P hNm e omega

/--
[PeriodicGraph.bufferedRestrict_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma bufferedRestrict_setOpen_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N : Nat}
  {e : Sym2 (P.BufferedVertex N)}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  P.bufferedRestrict N (setOpen (P.edgeIncl (P.bufferedRadius N) e) omega) = setOpen e (P.bufferedRestrict N omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRestrict_setOpen P N e omega

/--
[PeriodicGraph.bufferedRestrictLE_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma bufferedRestrictLE_setClosed_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N m : Nat}
  {e : Sym2 (P.BufferedVertex N)}
  {omega : ConfigSpace (Sym2 (P.BufferedVertex m))}
-- given
  (hNm : N <= m) :
-- imply
  P.bufferedRestrictLE hNm (setClosed (Sym2.map (P.bufferedVertexInclLE hNm) e) omega) = setClosed e (P.bufferedRestrictLE hNm omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRestrictLE_setClosed P hNm e omega

/--
[PeriodicGraph.bufferedRestrict_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma bufferedRestrict_setClosed_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N : Nat}
  {e : Sym2 (P.BufferedVertex N)}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  P.bufferedRestrict N (setClosed (P.edgeIncl (P.bufferedRadius N) e) omega) = setClosed e (P.bufferedRestrict N omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedRestrict_setClosed P N e omega

/--
[PeriodicGraph.freeBufferedMeasure_singleOpen_preimage_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma freeBufferedMeasure_singleOpen_preimage_bound_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N m : Nat}
  {p q : Real}
  {e : Sym2 (P.BufferedVertex N)}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hNm : N <= m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  cFE p q * (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N (setOpen e ⁻¹' S)) <= (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedMeasure_singleOpen_preimage_bound P hNm hp hp1 hq e S

/--
[PeriodicGraph.wiredBufferedMeasure_singleOpen_preimage_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma wiredBufferedMeasure_singleOpen_preimage_bound_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N m : Nat}
  {p q : Real}
  {e : Sym2 (P.BufferedVertex N)}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hNm : N <= m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  cFE p q * (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N (setOpen e ⁻¹' S)) <= (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedMeasure_singleOpen_preimage_bound P hNm hp hp1 hq e S

/--
[PeriodicGraph.freeBufferedInfiniteVolume_singleOpen_cylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_singleOpen_cylinder_bound_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N : Nat}
  {p q : Real}
  {e : Sym2 (P.BufferedVertex N)}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  cFE p q * (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N (setOpen e ⁻¹' S)) <= (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_singleOpen_cylinder_bound P N hp hp1 hq e S

/--
[PeriodicGraph.wiredBufferedInfiniteVolume_singleOpen_cylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_singleOpen_cylinder_bound_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N : Nat}
  {p q : Real}
  {e : Sym2 (P.BufferedVertex N)}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  cFE p q * (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N (setOpen e ⁻¹' S)) <= (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_singleOpen_cylinder_bound P N hp hp1 hq e S

/--
[PeriodicGraph.freeBufferedMeasure_singleClosed_preimage_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma freeBufferedMeasure_singleClosed_preimage_bound_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N m : Nat}
  {p q : Real}
  {e : Sym2 (P.BufferedVertex N)}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hNm : N <= m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  cFE p q * (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N (setClosed e ⁻¹' S)) <= (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedMeasure_singleClosed_preimage_bound P hNm hp hp1 hq e S

/--
[PeriodicGraph.freeBufferedInfiniteVolume_singleClosed_cylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_singleClosed_cylinder_bound_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N : Nat}
  {p q : Real}
  {e : Sym2 (P.BufferedVertex N)}
  {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  cFE p q * (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N (setClosed e ⁻¹' S)) <= (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_singleClosed_cylinder_bound P N hp hp1 hq e S

/--
[PeriodicGraph.freeBufferedInfiniteVolume_singleOpen_fullCylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_singleOpen_fullCylinder_bound_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {p q : Real}
  {e : Sym2 V}
  {C : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hC : C ∈ measurableCylinders (fun _ : Sym2 V => Bool)) :
-- imply
  cFE p q * (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (setOpen e ⁻¹' C) <= (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real C := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_singleOpen_fullCylinder_bound P hp hp1 hq e C hC

/--
[PeriodicGraph.wiredBufferedInfiniteVolume_singleOpen_fullCylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_singleOpen_fullCylinder_bound_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {p q : Real}
  {e : Sym2 V}
  {C : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hC : C ∈ measurableCylinders (fun _ : Sym2 V => Bool)) :
-- imply
  cFE p q * (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (setOpen e ⁻¹' C) <= (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real C := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_singleOpen_fullCylinder_bound P hp hp1 hq e C hC

/--
[PeriodicGraph.freeBufferedInfiniteVolume_singleClosed_fullCylinder_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_singleClosed_fullCylinder_bound_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {p q : Real}
  {e : Sym2 V}
  {C : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hC : C ∈ measurableCylinders (fun _ : Sym2 V => Bool)) :
-- imply
  cFE p q * (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (setClosed e ⁻¹' C) <= (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real C := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_singleClosed_fullCylinder_bound P hp hp1 hq e C hC

/--
[PeriodicGraph.freeBufferedInfiniteVolume_setOpen_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_setOpen_absolutelyContinuous_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {p q : Real}
  {e : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setOpen e) ≪ (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_setOpen_absolutelyContinuous P hp hp1 hq e

/--
[PeriodicGraph.wiredBufferedInfiniteVolume_setOpen_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_setOpen_absolutelyContinuous_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {p q : Real}
  {e : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setOpen e) ≪ (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_setOpen_absolutelyContinuous P hp hp1 hq e

/--
[PeriodicGraph.freeBufferedInfiniteVolume_setClosed_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_setClosed_absolutelyContinuous_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {p q : Real}
  {e : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setClosed e) ≪ (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_setClosed_absolutelyContinuous P hp hp1 hq e

/--
[PeriodicGraph.freeBufferedInfiniteVolume_setPattern_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_setPattern_absolutelyContinuous_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {p q : Real}
  {I : Finset (Sym2 V)}
  {eta : ConfigSpace ↥I}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setPattern I eta) ≪ (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_setPattern_absolutelyContinuous P hp hp1 hq I eta

/--
[forceOpenFinset_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma forceOpenFinset_insert_eq
  [Countable V]
  [DecidableEq V]
  {e : Sym2 V}
  {F : Finset (Sym2 V)} :
-- imply
  forceOpenFinset (insert e F) = setOpen e ∘ forceOpenFinset F := by
-- proof
  apply StatMech.FK.PeriodicPlanar.forceOpenFinset_insert e F

/--
[hasFiniteEnergy_of_singleOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma hasFiniteEnergy_of_singleOpen_eq
  [Countable V]
  [DecidableEq V]
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (hone : ∀ e : Sym2 V, mu.map (setOpen e) ≪ mu) :
-- imply
  HasFiniteEnergy mu := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hasFiniteEnergy_of_singleOpen mu hone

/--
[PeriodicGraph.freeBufferedInfiniteVolume_hasFiniteEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_hasFiniteEnergy_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  HasFiniteEnergy (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_hasFiniteEnergy P hp hp1 hq

/--
[PeriodicGraph.wiredBufferedInfiniteVolume_hasFiniteEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFiniteEnergy.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_hasFiniteEnergy_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  HasFiniteEnergy (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_hasFiniteEnergy P hp hp1 hq


-- created on 2026-10-23
