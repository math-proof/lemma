import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicReflection
open Filter Metric Set Topology StatMech StatMech.Universality StatMech.Universality.FKIsingCaratheodoryApproximation


/--
[mem_reflectComplexSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma mem_reflectComplexSet_eq
  {S : Set Complex}
  {z : Complex} :
-- imply
  z ∈ reflectComplexSet S ↔ (starRingEnd Complex) z ∈ S := by
-- proof
  apply StatMech.Universality.mem_reflectComplexSet

/--
[reflectComplexSet_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflectComplexSet_isOpen_eq
  {S : Set Complex}
-- given
  (hS : IsOpen S) :
-- imply
  IsOpen (reflectComplexSet S) := by
-- proof
  apply StatMech.Universality.reflectComplexSet_isOpen hS

/--
[reflectComplexSet_isPreconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflectComplexSet_isPreconnected_eq
  {S : Set Complex}
-- given
  (hS : IsPreconnected S) :
-- imply
  IsPreconnected (reflectComplexSet S) := by
-- proof
  apply StatMech.Universality.reflectComplexSet_isPreconnected hS

/--
[reflectComplexSet_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflectComplexSet_isCompact_eq
  {S : Set Complex}
-- given
  (hS : IsCompact S) :
-- imply
  IsCompact (reflectComplexSet S) := by
-- proof
  apply StatMech.Universality.reflectComplexSet_isCompact hS

/--
[reflectComplexSet_reflectComplexSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflectComplexSet_reflectComplexSet_eq
  {S : Set Complex} :
-- imply
  reflectComplexSet (reflectComplexSet S) = S := by
-- proof
  apply StatMech.Universality.reflectComplexSet_reflectComplexSet S

/--
[tendstoLocallyUniformlyOn_reflect_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma tendstoLocallyUniformlyOn_reflect_iff_eq
  {p : Filter ι}
  {F : ι → Complex → Complex}
  {f : Complex → Complex}
  {S : Set Complex} :
-- imply
  TendstoLocallyUniformlyOn (fun n z ↦ F n ((starRingEnd Complex) z)) (fun z ↦ f ((starRingEnd Complex) z)) p (reflectComplexSet S) ↔ TendstoLocallyUniformlyOn F f p S := by
-- proof
  apply StatMech.Universality.tendstoLocallyUniformlyOn_reflect_iff

/--
[closure_reflectComplexSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma closure_reflectComplexSet_eq
  {S : Set Complex} :
-- imply
  closure (reflectComplexSet S) = reflectComplexSet (closure S) := by
-- proof
  apply StatMech.Universality.closure_reflectComplexSet S

/--
[FKIsingDobrushinDomain.reflect_medialPosition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflect_medialPosition_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {e : M} :
-- imply
  D.reflect.medialPosition e = (starRingEnd Complex) (D.medialPosition e) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.reflect_medialPosition D e

/--
[FKIsingDobrushinDomain.reflect_fermionicObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflect_fermionicObservable_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {e : M} :
-- imply
  D.reflect.fermionicObservable e = D.fermionicObservable e := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.reflect_fermionicObservable D e

/--
[FKIsingDobrushinDomain.reflect_normalizedFermionicObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflect_normalizedFermionicObservable_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {mesh : Real}
  {e : M} :
-- imply
  D.reflect.normalizedFermionicObservable mesh e = D.normalizedFermionicObservable mesh e := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.reflect_normalizedFermionicObservable D mesh e

/--
[reflect_U](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflect_U_eq
  {A : FKIsingCaratheodoryApproximation} :
-- imply
  A.reflect.U = reflectComplexSet A.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.reflect_U A

/--
[reflect_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflect_root_eq
  {A : FKIsingCaratheodoryApproximation} :
-- imply
  A.reflect.root = (starRingEnd Complex) A.root := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.reflect_root A

/--
[reflect_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflect_carrier_eq
  {A : FKIsingCaratheodoryApproximation}
  {n : Nat} :
-- imply
  A.reflect.carrier n = reflectComplexSet (A.carrier n) := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.reflect_carrier A n

/--
[reflect_mesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflect_mesh_eq
  {A : FKIsingCaratheodoryApproximation}
  {n : Nat} :
-- imply
  A.reflect.mesh n = A.mesh n := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.reflect_mesh A n

/--
[reflect_medialEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflect_medialEmbedding_eq
  {A : FKIsingCaratheodoryApproximation}
  {n : Nat}
  {e : A.M n} :
-- imply
  A.reflect.medialEmbedding n e = (starRingEnd Complex) (A.medialEmbedding n e) := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.reflect_medialEmbedding A n e

/--
[reflect_rawInterpolant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflect_rawInterpolant_eq
  {A : FKIsingCaratheodoryApproximation}
  {n : Nat}
  {z : Complex} :
-- imply
  A.reflect.rawInterpolant n z = A.rawInterpolant n ((starRingEnd Complex) z) := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.reflect_rawInterpolant A n z

/--
[reflect_normalizedInterpolant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean)
-/
@[path]
private lemma reflect_normalizedInterpolant_eq
  {A : FKIsingCaratheodoryApproximation}
  {n : Nat}
  {z : Complex} :
-- imply
  A.reflect.normalizedInterpolant n z = A.normalizedInterpolant n ((starRingEnd Complex) z) := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.reflect_normalizedInterpolant A n z


-- created on 2026-10-23
