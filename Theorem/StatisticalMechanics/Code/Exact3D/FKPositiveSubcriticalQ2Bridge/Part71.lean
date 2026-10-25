/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part73
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

@[simp] theorem finiteBoundaryGhostSimonWeight_some_none_of_boundary
    (β H : ℝ) (n : ℕ) {v : FK.boxVerts 3 n}
    (hv : FK.boxBoundary 3 n v) :
    finiteBoundaryGhostSimonWeight β H n (some v) none =
      Real.tanh (β * H) *
        Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (Sharpness.couplingIn
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (finiteBoundaryGhostOriginalSet 3 n))
          ({some (IsingFK.boxOrigin 3 n), some v} :
            Finset (Option (FK.boxVerts 3 n))) := by
  classical
  simp [finiteBoundaryGhostSimonWeight, Sharpness.simonWeight, hv]

@[simp] theorem finiteBoundaryGhostSimonWeight_some_none_of_not_boundary
    (β H : ℝ) (n : ℕ) {v : FK.boxVerts 3 n}
    (hv : ¬ FK.boxBoundary 3 n v) :
    finiteBoundaryGhostSimonWeight β H n (some v) none = 0 := by
  classical
  simp [finiteBoundaryGhostSimonWeight, Sharpness.simonWeight, hv]


theorem finiteBoundaryGhostSimonWeight_sum_originalSet_eq_boundarySum
    (β H : ℝ) (n : ℕ) :
    (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
      finiteBoundaryGhostSimonWeight β H n x none) =
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        finiteBoundaryGhostSimonWeight β H n (some v) none := by
  classical
  unfold finiteBoundaryGhostOriginalSet
  rw [Finset.sum_image]
  · rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (FK.boxVerts 3 n)) (FK.boxBoundary 3 n)
      (fun v => finiteBoundaryGhostSimonWeight β H n (some v) none)]
    have hzero :
        (∑ v ∈ (Finset.univ : Finset (FK.boxVerts 3 n)).filter
          (fun v => ¬ FK.boxBoundary 3 n v),
        finiteBoundaryGhostSimonWeight β H n (some v) none) = 0 := by
      exact Finset.sum_eq_zero fun v hv => by
        rw [Finset.mem_filter] at hv
        exact finiteBoundaryGhostSimonWeight_some_none_of_not_boundary β H n
          hv.2
    rw [hzero]
    simp
  · intro a _ha b _hb hab
    exact Option.some.inj hab


theorem finiteBoundaryGhostSimonWeight_boundarySum_eq_tanh_mul_localizedSum
    (β H : ℝ) (n : ℕ) :
    (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
      finiteBoundaryGhostSimonWeight β H n (some v) none) =
      Real.tanh (β * H) *
        ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (Sharpness.couplingIn
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (finiteBoundaryGhostOriginalSet 3 n))
            ({some (IsingFK.boxOrigin 3 n), some v} :
              Finset (Option (FK.boxVerts 3 n))) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro v hv
  rw [Finset.mem_filter] at hv
  simp [hv.2]


theorem finiteBoundaryGhostSimonWeight_sum_zeroField_eq_zero
    (β : ℝ) (n : ℕ) :
    (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
      finiteBoundaryGhostSimonWeight β (0 : ℝ) n x none) = 0 := by
  rw [finiteBoundaryGhostSimonWeight_sum_originalSet_eq_boundarySum]
  rw [finiteBoundaryGhostSimonWeight_boundarySum_eq_tanh_mul_localizedSum]
  simp


theorem finiteBoundaryGhostSimonWeight_sum_le_currentBoundaryTwoPointSum_of_localization
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hloc :
      ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
        Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (Sharpness.couplingIn
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (finiteBoundaryGhostOriginalSet 3 n))
          ({some (IsingFK.boxOrigin 3 n), some v} :
            Finset (Option (FK.boxVerts 3 n)))
          ≤
        Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1)
          (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v})) :
    (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
      finiteBoundaryGhostSimonWeight β H n x none) ≤
      finiteCurrentBoundaryTwoPointSum β n := by
  classical
  have hbaseJ :
      ∀ e, 0 ≤
        boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hH
      (fun _ => by norm_num)
  have hcouplingIn :
      ∀ e, 0 ≤
        Sharpness.couplingIn
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOriginalSet 3 n) e := by
    intro e
    unfold Sharpness.couplingIn
    by_cases he :
        Sharpness.edgeInside (finiteBoundaryGhostOriginalSet 3 n) e
    · simp [he, hbaseJ e]
    · simp [he]
  have htanh_le : Real.tanh (β * H) ≤ 1 :=
    le_of_lt (Real.tanh_lt_one (β * H))
  rw [finiteBoundaryGhostSimonWeight_sum_originalSet_eq_boundarySum]
  rw [finiteCurrentBoundaryTwoPointSum_eq_expectationJBoundarySum]
  refine Finset.sum_le_sum ?_
  intro v hv
  have hvbdry : FK.boxBoundary 3 n v := by
    exact (Finset.mem_filter.mp hv).2
  let loc : ℝ :=
    Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (Sharpness.couplingIn
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOriginalSet 3 n))
      ({some (IsingFK.boxOrigin 3 n), some v} :
        Finset (Option (FK.boxVerts 3 n)))
  have hloc_nonneg : 0 ≤ loc := by
    dsimp [loc]
    exact Sharpness.ssl_expectationJ_nonneg
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (Sharpness.couplingIn
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOriginalSet 3 n))
      hβ hcouplingIn
      ({some (IsingFK.boxOrigin 3 n), some v} :
        Finset (Option (FK.boxVerts 3 n)))
  calc
    finiteBoundaryGhostSimonWeight β H n (some v) none
        = Real.tanh (β * H) * loc := by
          dsimp [loc]
          exact finiteBoundaryGhostSimonWeight_some_none_of_boundary
            β H n hvbdry
    _ ≤ 1 * loc := mul_le_mul_of_nonneg_right htanh_le hloc_nonneg
    _ = loc := by simp
    _ ≤ Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1)
          (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v}) := by
      dsimp [loc]
      exact hloc v hv


theorem finiteBoundaryGhostCurrentOnePoint_le_simonWeightSum_of_singletonSimonLieb
    {β H : ℝ} {n : ℕ}
    (hSL :
      Sharpness.SimonLieb
        (fun a b : Option (FK.boxVerts 3 n) =>
          Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b}))
        (some (IsingFK.boxOrigin 3 n))
        (finiteBoundaryGhostOriginalSet 3 n)
        (finiteBoundaryGhostSimonWeight β H n)
        ({none} : Finset (Option (FK.boxVerts 3 n)))) :
    finiteBoundaryGhostCurrentOnePoint 3 n β H ≤
      ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
        finiteBoundaryGhostSimonWeight β H n x none := by
  classical
  rw [finiteBoundaryGhostCurrentOnePoint_eq_expectationJ]
  rw [finiteBoundaryGhostOnePointSource_eq_symmDiff]
  exact
    simonLieb_singletonTarget_bound_expectationJ_symmDiff
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (o := some (IsingFK.boxOrigin 3 n))
      (z := none)
      (S := finiteBoundaryGhostOriginalSet 3 n)
      (w := finiteBoundaryGhostSimonWeight β H n)
      hSL
      (none_not_mem_finiteBoundaryGhostOriginalSet 3 n)


theorem finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLieb
    {β H : ℝ} {n : ℕ}
    (hSL :
      Sharpness.SimonLieb
        (fun a b : Option (FK.boxVerts 3 n) =>
          Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b}))
        (some (IsingFK.boxOrigin 3 n))
        (finiteBoundaryGhostOriginalSet 3 n)
        (finiteBoundaryGhostSimonWeight β H n)
        ({none} : Finset (Option (FK.boxVerts 3 n))))
    (hsum :
      (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
        finiteBoundaryGhostSimonWeight β H n x none) ≤
        finiteCurrentBoundaryTwoPointSum β n) :
    finiteBoundaryGhostCurrentOnePoint 3 n β H ≤
      finiteCurrentBoundaryTwoPointSum β n :=
  le_trans
    (finiteBoundaryGhostCurrentOnePoint_le_simonWeightSum_of_singletonSimonLieb
      hSL)
    hsum


theorem finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLiebLocalization
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hSL :
      Sharpness.SimonLieb
        (fun a b : Option (FK.boxVerts 3 n) =>
          Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b}))
        (some (IsingFK.boxOrigin 3 n))
        (finiteBoundaryGhostOriginalSet 3 n)
        (finiteBoundaryGhostSimonWeight β H n)
        ({none} : Finset (Option (FK.boxVerts 3 n))))
    (hloc :
      ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
        Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (Sharpness.couplingIn
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (finiteBoundaryGhostOriginalSet 3 n))
          ({some (IsingFK.boxOrigin 3 n), some v} :
            Finset (Option (FK.boxVerts 3 n)))
          ≤
        Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1)
          (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v})) :
    finiteBoundaryGhostCurrentOnePoint 3 n β H ≤
      finiteCurrentBoundaryTwoPointSum β n :=
  finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLieb
    hSL
    (finiteBoundaryGhostSimonWeight_sum_le_currentBoundaryTwoPointSum_of_localization
      hβ hH hloc)


theorem finiteBoundaryGhostSimonWeight_sum_le_currentBoundaryTwoPointSum
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H) :
    (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
      finiteBoundaryGhostSimonWeight β H n x none) ≤
      finiteCurrentBoundaryTwoPointSum β n :=
  finiteBoundaryGhostSimonWeight_sum_le_currentBoundaryTwoPointSum_of_localization
    hβ hH
    (fun _v hv =>
      finiteBoundaryGhostLocalizedExpectation_boundary_le_boxExpectation
        β H n (Finset.mem_filter.mp hv).2)


theorem finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLieb'
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hSL :
      Sharpness.SimonLieb
        (fun a b : Option (FK.boxVerts 3 n) =>
          Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b}))
        (some (IsingFK.boxOrigin 3 n))
        (finiteBoundaryGhostOriginalSet 3 n)
        (finiteBoundaryGhostSimonWeight β H n)
        ({none} : Finset (Option (FK.boxVerts 3 n)))) :
    finiteBoundaryGhostCurrentOnePoint 3 n β H ≤
      finiteCurrentBoundaryTwoPointSum β n :=
  finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLieb
    hSL
    (finiteBoundaryGhostSimonWeight_sum_le_currentBoundaryTwoPointSum hβ hH)


theorem finiteBoundaryGhostSingletonSimonLieb_of_scalarBound
    {β H : ℝ} {n : ℕ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hbound :
      Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {none})
      ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
          finiteBoundaryGhostSimonWeight β H n x none) :
    Sharpness.SimonLieb
      (fun a b : Option (FK.boxVerts 3 n) =>
        Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b}))
      (some (IsingFK.boxOrigin 3 n))
      (finiteBoundaryGhostOriginalSet 3 n)
      (finiteBoundaryGhostSimonWeight β H n)
      ({none} : Finset (Option (FK.boxVerts 3 n))) := by
  classical
  have hbaseJ :
      ∀ e, 0 ≤
        boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hH
      (fun _ => by norm_num)
  have hcouplingIn :
      ∀ e, 0 ≤
        Sharpness.couplingIn
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOriginalSet 3 n) e := by
    intro e
    unfold Sharpness.couplingIn
    by_cases he :
        Sharpness.edgeInside (finiteBoundaryGhostOriginalSet 3 n) e
    · simp [he, hbaseJ e]
    · simp [he]
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    exact Sharpness.ssl_expectationJ_nonneg
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      hβ hbaseJ
      (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b})
  · have hcorr :
        ∀ x, 0 ≤
          Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (Sharpness.couplingIn
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (finiteBoundaryGhostOriginalSet 3 n))
            ({some (IsingFK.boxOrigin 3 n), x} :
              Finset (Option (FK.boxVerts 3 n))) := by
      intro x
      exact Sharpness.ssl_expectationJ_nonneg
        (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (Sharpness.couplingIn
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (finiteBoundaryGhostOriginalSet 3 n))
        hβ hcouplingIn
        ({some (IsingFK.boxOrigin 3 n), x} :
          Finset (Option (FK.boxVerts 3 n)))
    simpa [finiteBoundaryGhostSimonWeight] using
      Sharpness.simonWeight_nonneg
        (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (finiteBoundaryGhostOriginalSet 3 n)
        (some (IsingFK.boxOrigin 3 n)) hβ hbaseJ hcorr
  · intro z hz
    have hz_none : z = none := by
      rcases z with _ | v
      · rfl
      · exact False.elim (hz (some_mem_finiteBoundaryGhostOriginalSet 3 n v))
    subst z
    have hnone :
        Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n))) = 1 :=
      expectationJ_empty_eq_one (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
    simpa [hnone] using hbound


end Exact3D
end StatMech
