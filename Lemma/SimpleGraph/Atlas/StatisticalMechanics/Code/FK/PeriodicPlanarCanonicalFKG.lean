import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.freeBufferedMeasure_fkg_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFKG.lean)
-/
@[path]
private lemma freeBufferedMeasure_fkg_cylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N m : Nat}
  {p q : Real}
  {A B : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hNm : N <= m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N A) * (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N B) <= (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N (A ∩ B)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedMeasure_fkg_cylinder P N m hNm hp hp1 hq hA hB

/--
[PeriodicGraph.wiredBufferedMeasure_fkg_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFKG.lean)
-/
@[path]
private lemma wiredBufferedMeasure_fkg_cylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N m : Nat}
  {p q : Real}
  {A B : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hNm : N <= m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N A) * (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N B) <= (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N (A ∩ B)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedMeasure_fkg_cylinder P N m hNm hp hp1 hq hA hB

/--
[PeriodicGraph.freeBufferedInfiniteVolume_fkg_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFKG.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_fkg_cylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N : Nat}
  {p q : Real}
  {A B : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  let mu := (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real (P.bufferedCylinder N A) * mu.real (P.bufferedCylinder N B) <= mu.real (P.bufferedCylinder N (A ∩ B)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_fkg_cylinder P N hp hp1 hq hA hB

/--
[PeriodicGraph.wiredBufferedInfiniteVolume_fkg_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFKG.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_fkg_cylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N : Nat}
  {p q : Real}
  {A B : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  let mu := (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real (P.bufferedCylinder N A) * mu.real (P.bufferedCylinder N B) <= mu.real (P.bufferedCylinder N (A ∩ B)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_fkg_cylinder P N hp hp1 hq hA hB

/--
[PeriodicGraph.freeBufferedInfiniteVolume_fkg_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFKG.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_fkg_isClopen_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
  {A B : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hAcl : IsClopen A)
  (hBcl : IsClopen B)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  let mu := (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real A * mu.real B <= mu.real (A ∩ B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_fkg_isClopen P hp hp1 hq hAcl hBcl hA hB

/--
[PeriodicGraph.wiredBufferedInfiniteVolume_fkg_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFKG.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_fkg_isClopen_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
  {A B : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hAcl : IsClopen A)
  (hBcl : IsClopen B)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  let mu := (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real A * mu.real B <= mu.real (A ∩ B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_fkg_isClopen P hp hp1 hq hAcl hBcl hA hB

/--
[PeriodicGraph.freeBufferedInfiniteVolume_isFKG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFKG.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_isFKG_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  let mu := (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) IsFKG mu := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_isFKG P hp hp1 hq

/--
[PeriodicGraph.wiredBufferedInfiniteVolume_isFKG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFKG.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_isFKG_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  let mu := (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) IsFKG mu := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_isFKG P hp hp1 hq

/--
[PeriodicGraph.freeBufferedInfiniteVolume_fkg_iInter_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFKG.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_fkg_iInter_isClopen_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (A B : Nat -> Set (ConfigSpace (Sym2 V)))
  (hAcl : forall n, IsClopen (A n))
  (hBcl : forall n, IsClopen (B n))
  (hA : forall n, IsIncreasing (A n))
  (hB : forall n, IsIncreasing (B n))
  (hantiA : Antitone A)
  (hantiB : Antitone B) :
-- imply
  let mu := (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real (iInter A) * mu.real (iInter B) <= mu.real (iInter A ∩ iInter B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_fkg_iInter_isClopen P hp hp1 hq A B hAcl hBcl hA hB hantiA hantiB

/--
[PeriodicGraph.wiredBufferedInfiniteVolume_fkg_iInter_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFKG.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_fkg_iInter_isClopen_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (A B : Nat -> Set (ConfigSpace (Sym2 V)))
  (hAcl : forall n, IsClopen (A n))
  (hBcl : forall n, IsClopen (B n))
  (hA : forall n, IsIncreasing (A n))
  (hB : forall n, IsIncreasing (B n))
  (hantiA : Antitone A)
  (hantiB : Antitone B) :
-- imply
  let mu := (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real (iInter A) * mu.real (iInter B) <= mu.real (iInter A ∩ iInter B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_fkg_iInter_isClopen P hp hp1 hq A B hAcl hBcl hA hB hantiA hantiB

/--
[PeriodicGraph.wiredBufferedInfiniteVolume_fkg_iInter_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFKG.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_fkg_iInter_cylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (N : Nat -> Nat)
  (A B : (n : Nat) -> Set (ConfigSpace (Sym2 (P.BufferedVertex (N n)))))
  (hA : forall n, IsIncreasing (A n))
  (hB : forall n, IsIncreasing (B n))
  (hantiA : Antitone (fun n => P.bufferedCylinder (N n) (A n)))
  (hantiB : Antitone (fun n => P.bufferedCylinder (N n) (B n))) :
-- imply
  let mu := (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real (iInter fun n => P.bufferedCylinder (N n) (A n)) * mu.real (iInter fun n => P.bufferedCylinder (N n) (B n)) <= mu.real ((iInter fun n => P.bufferedCylinder (N n) (A n)) ∩ (iInter fun n => P.bufferedCylinder (N n) (B n))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_fkg_iInter_cylinder P hp hp1 hq N A B hA hB hantiA hantiB

/--
[PeriodicGraph.freeBufferedInfiniteVolume_fkg_iInter_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalFKG.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_fkg_iInter_cylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (N : Nat -> Nat)
  (A B : (n : Nat) -> Set (ConfigSpace (Sym2 (P.BufferedVertex (N n)))))
  (hA : forall n, IsIncreasing (A n))
  (hB : forall n, IsIncreasing (B n))
  (hantiA : Antitone (fun n => P.bufferedCylinder (N n) (A n)))
  (hantiB : Antitone (fun n => P.bufferedCylinder (N n) (B n))) :
-- imply
  let mu := (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real (iInter fun n => P.bufferedCylinder (N n) (A n)) * mu.real (iInter fun n => P.bufferedCylinder (N n) (B n)) <= mu.real ((iInter fun n => P.bufferedCylinder (N n) (A n)) ∩ (iInter fun n => P.bufferedCylinder (N n) (B n))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_fkg_iInter_cylinder P hp hp1 hq N A B hA hB hantiA hantiB


-- created on 2026-10-23
