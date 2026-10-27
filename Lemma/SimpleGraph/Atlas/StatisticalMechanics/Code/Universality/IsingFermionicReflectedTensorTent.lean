import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
open Filter Metric Set Topology StatMech StatMech.Universality StatMech.Universality.FKIsingCaratheodoryApproximation


/--
[BoundaryRadialTensorTentGeometry.reflectedInterpolant_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectedTensorTent.lean)
-/
@[path]
private lemma reflectedInterpolant_continuous_eq
  {A : FKIsingCaratheodoryApproximation}
  {G : BoundaryRadialTensorTentGeometry A}
  {n : Nat} :
-- imply
  Continuous (G.reflectedInterpolant A n) := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.BoundaryRadialTensorTentGeometry.reflectedInterpolant_continuous A G n

/--
[BoundaryRadialTensorTentGeometry.reflected_projectedMedial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectedTensorTent.lean)
-/
@[path]
private lemma reflected_projectedMedial_eq
  {A : FKIsingCaratheodoryApproximation}
  {G : BoundaryRadialTensorTentGeometry A}
  {n : Nat}
  {e : A.reflect.M n} :
-- imply
  isingProj (G.reflectedTangent A n e) (G.reflectedInterpolant A n (A.reflect.medialEmbedding n e)) = @FKIsingDobrushinDomain.normalizedFermionicObservable (A.reflect.P n) (A.reflect.M n) (A.reflect.decEqM n) (A.reflect.dobrushin n) (A.reflect.mesh n) e := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.BoundaryRadialTensorTentGeometry.reflected_projectedMedial A G n e

/--
[MeshUniformCompactHolder.reflected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectedTensorTent.lean)
-/
@[path]
private lemma reflected_eq
  {A : FKIsingCaratheodoryApproximation}
  {G : BoundaryRadialTensorTentGeometry A}
  {F : Nat → Complex → Complex}
  {H : A.MeshUniformCompactHolder F} :
-- imply
  A.reflect.MeshUniformCompactHolder (fun n z ↦ F n ((starRingEnd Complex) z)) := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.MeshUniformCompactHolder.reflected A G H

/--
[BoundaryRadialTensorTentGeometry.reflected_tendsto_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectedTensorTent.lean)
-/
@[path]
private lemma reflected_tendsto_iff_eq
  {A : FKIsingCaratheodoryApproximation}
  {G : BoundaryRadialTensorTentGeometry A}
  {f : Complex → Complex} :
-- imply
  TendstoLocallyUniformlyOn (G.reflectedInterpolant A) (fun z ↦ f ((starRingEnd Complex) z)) atTop (reflectComplexSet A.U) ↔ TendstoLocallyUniformlyOn (BoundaryRadialTensorTentGeometry.interpolant A G) f atTop A.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.BoundaryRadialTensorTentGeometry.reflected_tendsto_iff A G


-- created on 2026-10-23
