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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part44
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_fiber_dataWeight
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n) :
    Finset.sum
        (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
          m v hsrc).domain
      (fun a =>
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
          ((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
            m v hsrc).map a)) =
      Finset.sum
        (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
          m v hsrc).image
        (fun d =>
          (((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
            m v hsrc).fiber d).card : ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
  exact
    FinsetFiberIndex.sum_fiber_weight
      (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
        m v hsrc)
      (finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H)

set_option maxHeartbeats 1500000 in


theorem
    finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_fiber_card_le_boundaryGhostMultiplicity
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n)
    (d : finiteBoundaryGhostCollapsedTwoPointSourceData n v) :
    ((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
      m v hsrc).fiber d).card ≤
      m ⟨s(some v, none), by
        rw [SimpleGraph.mem_edgeFinset]
        simp [Sharpness.withGhost]⟩ := by
  classical
  letI : DecidableEq (finiteBoundaryGhostCollapsedTwoPointSourceData n v) :=
    Classical.decEq _
  letI : DecidableEq (finiteBoundaryGhostTwoPointSourceData n v) :=
    Classical.decEq _
  refine (Finset.card_le_card ?_).trans
    (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_boundaryGhostMultiplicity
      m v d.toSourceData)
  intro p hp
  have hpmap :
      (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
        m v hsrc).map p = d := by
    exact ((FinsetFiberIndex.mem_fiber
      (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
        m v hsrc) d p).mp hp).2
  have hpold :
      finiteBoundaryGhostBoundaryCrossingPairDecrementData
        (p := p.1) m v p.2 = d.toSourceData := by
    simpa [finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex] using
      congrArg finiteBoundaryGhostCollapsedTwoPointSourceData.toSourceData hpmap
  exact (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_mem
    m v d.toSourceData p).mpr hpold


theorem
    finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_dataWeight_le_boundaryGhostMultiplicity_mul_image_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n) :
    Finset.sum
        (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
          m v hsrc).domain
      (fun a =>
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
          ((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
            m v hsrc).map a))
      ≤
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          Finset.sum
            (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
              m v hsrc).image
            (fun d =>
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
  classical
  let eGhost : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset :=
    ⟨s(some v, none), by
      rw [SimpleGraph.mem_edgeFinset]
      simp [Sharpness.withGhost]⟩
  let I := finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
    m v hsrc
  change
    Finset.sum I.domain
        (fun a =>
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H (I.map a)) ≤
      (m eGhost : ℝ) *
        Finset.sum I.image
          (fun d => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  refine
    FinsetFiberIndex.sum_le_const_mul_image_sum_of_fiber_card_le
      I (finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H) ?_ ?_
  · intro d _hd
    have hcard :
        (I.fiber d).card ≤ m eGhost := by
      simpa [I, eGhost] using
        finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_fiber_card_le_boundaryGhostMultiplicity
          m v hsrc d
    exact_mod_cast hcard
  · intro d _hd
    exact finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_nonneg hβ hH d


theorem
    finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_fiber_weight_le_boundaryGhostMultiplicity_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n) :
    Finset.sum
        (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
          m v hsrc).image
        (fun d =>
          (((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
            m v hsrc).fiber d).card : ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
      ≤
        ∑ d ∈ (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
          m v hsrc).image,
          (m ⟨s(some v, none), by
            rw [SimpleGraph.mem_edgeFinset]
            simp [Sharpness.withGhost]⟩ : ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
  classical
  refine Finset.sum_le_sum ?_
  intro d _hd
  have hcard :
      (((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
        m v hsrc).fiber d).card : ℝ) ≤
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) := by
    exact_mod_cast
      finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_fiber_card_le_boundaryGhostMultiplicity
        m v hsrc d
  exact
    mul_le_mul_of_nonneg_right hcard
      (finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_nonneg hβ hH d)


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_image_eq
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).image =
      finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v := by
  classical
  letI : DecidableEq (finiteBoundaryGhostTwoPointSourceData n v) :=
    Classical.decEq _
  rfl


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_fiber_eq
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (d : finiteBoundaryGhostTwoPointSourceData n v) :
    (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).fiber d =
      finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d := by
  classical
  letI : DecidableEq (finiteBoundaryGhostTwoPointSourceData n v) :=
    Classical.decEq _
  rfl


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_dataWeight_indexDomain
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).domain
      (fun a =>
        finiteBoundaryGhostTwoPointSourceDataWeight β H
          ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).map a)) =
      Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v)
        (fun d =>
          ((finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card :
            ℝ) *
            finiteBoundaryGhostTwoPointSourceDataWeight β H d) := by
  rw [← finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_image_eq m v]
  exact
    finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_fiber_dataWeight
      m v


end Exact3D
end StatMech
