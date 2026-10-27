import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQInfiniteFKG
open MeasureTheory Filter Topology SimpleGraph StatMech.Lattice StatMech.IsingFK StatMech StatMech.FK


/--
[fkgq_freeFiniteMeasure_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQInfiniteFKG.lean)
-/
@[path]
private lemma fkgq_freeFiniteMeasure_fkg_eq
  {d : Nat}
  {N m : Nat}
  {p q : Real}
  {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N <= m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hS₁ : IsIncreasing S₁)
  (hS₂ : IsIncreasing S₂) :
-- imply
  (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S₁) * (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S₂) <= (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
-- proof
  apply StatMech.FK.fkgq_freeFiniteMeasure_fkg N m hNm hp hp1 hq hS₁ hS₂

/--
[fkgq_freeInfiniteVolume_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQInfiniteFKG.lean)
-/
@[path]
private lemma fkgq_freeInfiniteVolume_fkg_eq
  {d : Nat}
  {N : Nat}
  {p q : Real}
  {S₁ S₂ : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hS₁ : IsIncreasing S₁)
  (hS₂ : IsIncreasing S₂) :
-- imply
  (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S₁) * (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S₂) <= (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S₁ ∩ boxRestrict d N ⁻¹' S₂) := by
-- proof
  apply StatMech.FK.fkgq_freeInfiniteVolume_fkg N hp hp1 hq hS₁ hS₂

/--
[fkgq_freeInfiniteVolume_fkg_of_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQInfiniteFKG.lean)
-/
@[path]
private lemma fkgq_freeInfiniteVolume_fkg_of_dependsOn_eq
  {d : Nat}
  {N : Nat}
  {p q : Real}
  {A B : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hAdep : StatMech.DependsOn A (Set.range (edgeIncl d N)))
  (hBdep : StatMech.DependsOn B (Set.range (edgeIncl d N)))
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real A * (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real B <= (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (A ∩ B) := by
-- proof
  apply StatMech.FK.fkgq_freeInfiniteVolume_fkg_of_dependsOn N hp hp1 hq hAdep hBdep hA hB

/--
[fkgq_freeInfiniteVolume_fkg_iInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQInfiniteFKG.lean)
-/
@[path]
private lemma fkgq_freeInfiniteVolume_fkg_iInter_eq
  {d : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (N : Nat -> Nat)
  (S₁ S₂ : (n : Nat) -> Set (ConfigSpace (Sym2 (boxVerts d (N n)))))
  (hS₁ : forall n, IsIncreasing (S₁ n))
  (hS₂ : forall n, IsIncreasing (S₂ n))
  (hanti₁ : Antitone (fun n => boxRestrict d (N n) ⁻¹' S₁ n))
  (hanti₂ : Antitone (fun n => boxRestrict d (N n) ⁻¹' S₂ n)) :
-- imply
  let mu := (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) mu.real (⋂ n, boxRestrict d (N n) ⁻¹' S₁ n) * mu.real (⋂ n, boxRestrict d (N n) ⁻¹' S₂ n) <= mu.real ((⋂ n, boxRestrict d (N n) ⁻¹' S₁ n) ∩ (⋂ n, boxRestrict d (N n) ⁻¹' S₂ n)) := by
-- proof
  apply StatMech.FK.fkgq_freeInfiniteVolume_fkg_iInter hp hp1 hq N S₁ S₂ hS₁ hS₂ hanti₁ hanti₂

/--
[fkgq_freeInfiniteVolume_fkg_iInter_of_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQInfiniteFKG.lean)
-/
@[path]
private lemma fkgq_freeInfiniteVolume_fkg_iInter_of_dependsOn_eq
  {d : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (N : Nat -> Nat)
  (A B : Nat -> Set (ConfigSpace (Sym2 (Site d))))
  (hAdep : forall n, StatMech.DependsOn (A n) (Set.range (edgeIncl d (N n))))
  (hBdep : forall n, StatMech.DependsOn (B n) (Set.range (edgeIncl d (N n))))
  (hA : forall n, IsIncreasing (A n))
  (hB : forall n, IsIncreasing (B n))
  (hAmeas : forall n, MeasurableSet (A n))
  (hBmeas : forall n, MeasurableSet (B n))
  (hantiA : Antitone A)
  (hantiB : Antitone B) :
-- imply
  let mu := (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) mu.real (⋂ n, A n) * mu.real (⋂ n, B n) <= mu.real ((⋂ n, A n) ∩ (⋂ n, B n)) := by
-- proof
  apply StatMech.FK.fkgq_freeInfiniteVolume_fkg_iInter_of_dependsOn hp hp1 hq N A B hAdep hBdep hA hB hAmeas hBmeas hantiA hantiB


-- created on 2026-10-23
