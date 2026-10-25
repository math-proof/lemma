/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectedTensorTent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflection.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent
open Filter Metric Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)

variable (G : BoundaryRadialTensorTentGeometry A)


theorem BoundaryRadialTensorTentGeometry.reflectedInterpolant_continuous
    (n : Nat) : Continuous (G.reflectedInterpolant A n) := by
  exact (G.interpolant_continuous A n).comp Complex.continuous_conj


theorem BoundaryRadialTensorTentGeometry.reflected_projectedMedial
    (n : Nat) (e : A.reflect.M n) :
    isingProj (G.reflectedTangent A n e)
        (G.reflectedInterpolant A n (A.reflect.medialEmbedding n e)) =
      @FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.reflect.P n) (A.reflect.M n) (A.reflect.decEqM n)
        (A.reflect.dobrushin n) (A.reflect.mesh n) e := by
  simpa [BoundaryRadialTensorTentGeometry.reflectedInterpolant,
    BoundaryRadialTensorTentGeometry.reflectedTangent] using
      G.projectedMedial A n e


theorem MeshUniformCompactHolder.reflected
    {F : Nat → Complex → Complex} (H : A.MeshUniformCompactHolder F) :
    A.reflect.MeshUniformCompactHolder
      (fun n z ↦ F n ((starRingEnd Complex) z)) := by
  refine { holder := ?_ }
  intro K hK hKU
  have hK' : IsCompact (reflectComplexSet K) :=
    reflectComplexSet_isCompact hK
  have hKU' : reflectComplexSet K ⊆ A.U := by
    intro z hz
    rw [mem_reflectComplexSet] at hz
    have hz' := hKU hz
    simpa using (mem_reflectComplexSet.mp hz')
  obtain ⟨C, alpha, halpha, hholder⟩ := H.holder _ hK' hKU'
  refine ⟨C, alpha, halpha, ?_⟩
  intro n x hx y hy
  have hx' : (starRingEnd Complex) x ∈ reflectComplexSet K :=
    mem_reflectComplexSet.mpr (by simpa using hx)
  have hy' : (starRingEnd Complex) y ∈ reflectComplexSet K :=
    mem_reflectComplexSet.mpr (by simpa using hy)
  have h := hholder n ((starRingEnd Complex) x) hx'
    ((starRingEnd Complex) y) hy'
  simpa [Complex.isometry_conj.edist_eq] using h


end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
