/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part25


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem radialPatchPrimal_exists_orderedDual
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (p : FKIsingSquareRadialPatchPrimalNode m) :
    ∃ q : FKIsingSquareRadialPatchDualNode m,
      radialPatchPrimalValue n m hn hm p ≤
        radialPatchDualValue n m hn hm hm2 q := by
  by_cases hi : p.1.1.1 + 1 < m
  · let q : FKIsingSquareRadialPatchDualNode m :=
      ⟨(⟨p.1.1.1 + 1, hi⟩, p.1.2), by
        change ¬ Even ((p.1.1.1 + 1) + p.1.2.1)
        rw [Nat.not_even_iff]
        have hpmod := Nat.even_iff.mp p.2
        omega⟩
    let e := fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm (by omega) p.1.1.1 p.1.2.1
    refine ⟨q, ?_⟩
    have h := fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face
      n hn e
    rw [fkIsingSquareRadialPatchHorizontal_endpoint_of_even
          n m hn hm (by omega) p.1.1.1 p.1.2.1 hi p.1.2.2 p.2,
        fkIsingSquareRadialPatchHorizontal_face_of_even
          n m hn hm (by omega) p.1.1.1 p.1.2.1 hi p.1.2.2 p.2] at h
    simpa [radialPatchPrimalValue, radialPatchDualValue, q, e] using h
  · have hi0 : 0 < p.1.1.1 := by
      have hip := p.1.1.2
      omega
    have hprev : p.1.1.1 - 1 + 1 < m := by
      have hip := p.1.1.2
      omega
    have hodd : ¬ Even (p.1.1.1 - 1 + p.1.2.1) := by
      rw [Nat.not_even_iff]
      have hpmod := Nat.even_iff.mp p.2
      omega
    let q : FKIsingSquareRadialPatchDualNode m :=
      ⟨(⟨p.1.1.1 - 1, by omega⟩, p.1.2), hodd⟩
    let e := fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm (by omega) (p.1.1.1 - 1) p.1.2.1
    refine ⟨q, ?_⟩
    have h := fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face
      n hn e
    rw [fkIsingSquareRadialPatchHorizontal_endpoint_of_odd
          n m hn hm (by omega) (p.1.1.1 - 1) p.1.2.1 hprev p.1.2.2 hodd,
        fkIsingSquareRadialPatchHorizontal_face_of_odd
          n m hn hm (by omega) (p.1.1.1 - 1) p.1.2.1 hprev p.1.2.2 hodd] at h
    have heq : p.1.1.1 - 1 + 1 = p.1.1.1 := by omega
    simpa [radialPatchPrimalValue, radialPatchDualValue, q, e, heq] using h


theorem radialPatchDual_exists_orderedPrimal
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (q : FKIsingSquareRadialPatchDualNode m) :
    ∃ p : FKIsingSquareRadialPatchPrimalNode m,
      radialPatchPrimalValue n m hn hm p ≤
        radialPatchDualValue n m hn hm hm2 q := by
  by_cases hi : q.1.1.1 + 1 < m
  · have heven : Even (q.1.1.1 + 1 + q.1.2.1) := by
      rw [Nat.even_iff]
      have hqmod := Nat.not_even_iff.mp q.2
      omega
    let p : FKIsingSquareRadialPatchPrimalNode m :=
      ⟨(⟨q.1.1.1 + 1, hi⟩, q.1.2), heven⟩
    let e := fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm (by omega) q.1.1.1 q.1.2.1
    refine ⟨p, ?_⟩
    have h := fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face
      n hn e
    rw [fkIsingSquareRadialPatchHorizontal_endpoint_of_odd
          n m hn hm (by omega) q.1.1.1 q.1.2.1 hi q.1.2.2 q.2,
        fkIsingSquareRadialPatchHorizontal_face_of_odd
          n m hn hm (by omega) q.1.1.1 q.1.2.1 hi q.1.2.2 q.2] at h
    simpa [radialPatchPrimalValue, radialPatchDualValue, p, e] using h
  · have hi0 : 0 < q.1.1.1 := by
      have hiq := q.1.1.2
      omega
    have hprev : q.1.1.1 - 1 + 1 < m := by
      have hiq := q.1.1.2
      omega
    have heven : Even (q.1.1.1 - 1 + q.1.2.1) := by
      rw [Nat.even_iff]
      have hqmod := Nat.not_even_iff.mp q.2
      omega
    let p : FKIsingSquareRadialPatchPrimalNode m :=
      ⟨(⟨q.1.1.1 - 1, by omega⟩, q.1.2), heven⟩
    let e := fkIsingSquareRadialPatchHorizontalIncidence
      n m hn hm (by omega) (q.1.1.1 - 1) q.1.2.1
    refine ⟨p, ?_⟩
    have h := fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face
      n hn e
    rw [fkIsingSquareRadialPatchHorizontal_endpoint_of_even
          n m hn hm (by omega) (q.1.1.1 - 1) q.1.2.1 hprev q.1.2.2 heven,
        fkIsingSquareRadialPatchHorizontal_face_of_even
          n m hn hm (by omega) (q.1.1.1 - 1) q.1.2.1 hprev q.1.2.2 heven] at h
    have heq : q.1.1.1 - 1 + 1 = q.1.1.1 := by omega
    simpa [radialPatchPrimalValue, radialPatchDualValue, p, e, heq] using h


theorem radialPatch_unitRange_of_fullSquareGhost
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) :
    (∀ p, 0 ≤ radialPatchPrimalValue n m hn hm p ∧
      radialPatchPrimalValue n m hn hm p ≤ 1) ∧
      (∀ q, 0 ≤ radialPatchDualValue n m hn hm hm2 q ∧
        radialPatchDualValue n m hn hm hm2 q ≤ 1) := by
  have hprimalLower : ∀ p, 0 ≤ radialPatchPrimalValue n m hn hm p := by
    intro p
    apply fkIsingSquareFullVertex_zero_le_of_modifiedSuperharmonic
      n (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
    · intro x hx
      exact vertex_modifiedLaplacian_nonpos_of_not_wiredArc n hn x hx
    · intro x hx
      exact vertex_fixedBoundary_nonneg n hn x hx
  have hdualUpper : ∀ q, radialPatchDualValue n m hn hm hm2 q ≤ 1 := by
    intro q
    apply fkIsingSquareFullFace_le_one_of_modifiedSubharmonic
      n (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
    · intro c hc
      exact face_modifiedLaplacian_nonneg_of_not_fixedBoundary n hn c hc
    · intro c hc
      exact face_fixedBoundary_le_one n hn c hc
  constructor
  · intro p
    obtain ⟨q, hpq⟩ := radialPatchPrimal_exists_orderedDual
      n m hn hm hm2 p
    exact ⟨hprimalLower p, hpq.trans (hdualUpper q)⟩
  · intro q
    obtain ⟨p, hpq⟩ := radialPatchDual_exists_orderedPrimal
      n m hn hm hm2 q
    exact ⟨(hprimalLower p).trans hpq, hdualUpper q⟩

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
