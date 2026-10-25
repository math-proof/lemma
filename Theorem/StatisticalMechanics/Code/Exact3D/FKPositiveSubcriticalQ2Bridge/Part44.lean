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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part45
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_dataWeight
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
    finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight β H m v p =
      finiteBoundaryGhostTwoPointSourceDataWeight β H
        (finiteBoundaryGhostBoundaryCrossingPairDecrementData
          (p := p) m v hp) := by
  unfold finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
  have hsource :=
    finiteBoundaryGhostBoundaryCrossingPairs_decremented_source m v hp
  rw [if_pos hsource, one_mul]
  rfl


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeightSum_eq_indexDomain
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
      (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight β H m v) =
      Finset.sum ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).domain)
        (fun a =>
          finiteBoundaryGhostTwoPointSourceDataWeight β H
            ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).map a)) := by
  classical
  rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intro a _ha
  simpa [finiteBoundaryGhostBoundaryCrossingPairDecrementIndex] using
    (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_dataWeight
      (β := β) (H := H) m (v := v) a.2)


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_card_le_boundaryGhostMultiplicity_sum
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    (∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
        (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card) ≤
      ∑ _d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
        m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ := by
  classical
  refine Finset.sum_le_sum ?_
  intro d _hd
  exact
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_boundaryGhostMultiplicity
      m v d


theorem finiteBoundaryGhostBoundaryCrossingPairs_card_le_decrementImage_card_mul_boundaryGhostMultiplicity
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    (finiteBoundaryGhostBoundaryCrossingPairs m v).card ≤
      (finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v).card *
        m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let eGhost : ↥G.edgeFinset :=
    ⟨s(some v, none), by
      rw [SimpleGraph.mem_edgeFinset]
      simp [G, Sharpness.withGhost]⟩
  change
    (finiteBoundaryGhostBoundaryCrossingPairs m v).card ≤
      (finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v).card *
        m eGhost
  calc
    (finiteBoundaryGhostBoundaryCrossingPairs m v).card =
        ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
          (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card :=
      finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_card m v
    _ ≤
        ∑ _d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
          m eGhost := by
      refine Finset.sum_le_sum ?_
      intro d _hd
      simpa [G, eGhost] using
        finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_boundaryGhostMultiplicity
          m v d
    _ =
        (finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v).card *
          m eGhost := by
      rw [Finset.sum_const]
      rw [nsmul_eq_mul]
      rw [Nat.cast_id]


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_weight_le_boundaryGhostMultiplicity_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    (∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
        ((finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card :
          ℝ) *
          finiteBoundaryGhostTwoPointSourceDataWeight β H d) ≤
      ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          finiteBoundaryGhostTwoPointSourceDataWeight β H d := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let eGhost : ↥G.edgeFinset :=
    ⟨s(some v, none), by
      rw [SimpleGraph.mem_edgeFinset]
      simp [G, Sharpness.withGhost]⟩
  change
    (∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
        ((finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card :
          ℝ) *
          finiteBoundaryGhostTwoPointSourceDataWeight β H d) ≤
      ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
        (m eGhost : ℝ) *
          finiteBoundaryGhostTwoPointSourceDataWeight β H d
  refine Finset.sum_le_sum ?_
  intro d _hd
  have hcard :
      ((finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card :
        ℝ) ≤ (m eGhost : ℝ) := by
    exact_mod_cast
      (by
        simpa [G, eGhost] using
          finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_boundaryGhostMultiplicity
            m v d)
  exact
    mul_le_mul_of_nonneg_right hcard
      (finiteBoundaryGhostTwoPointSourceDataWeight_nonneg hβ hH d)


theorem finiteBoundaryGhost_weight_decrement_boundaryGhostCopy
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m}
    (hvbdry : FK.boxBoundary 3 n v)
    (hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
    ((m i.1 : ℝ) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
      (β * H) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
            (Function.update m i.1 (m i.1 - 1))) := by
  classical
  have hmpos : 0 < m i.1 :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) i.2.2
  have hJedge :
      boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) i.1.1 = H := by
    have hJends :
        boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m i) = H := by
      rw [hends]
      exact boundaryGhostCoupling_some_none_of_boundary
        (FK.boxBoundary 3 n) (fun _ => (1 : ℝ)) hvbdry
    simpa [Sharpness.FluxEdgeCopy.endsM] using hJends
  simpa [hJedge] using
    weight_ofEdgeFun_decrement
      (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      m i.1 hmpos


theorem finiteBoundaryGhostBoundaryCrossingPairs_weight_decrement
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
    ((m p.2.1 : ℝ) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
      (β * H) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
            (Function.update m p.2.1 (m p.2.1 - 1))) := by
  classical
  obtain ⟨_hKsrc, _hiK, hsome, hnone⟩ :=
    (finiteBoundaryGhostBoundaryCrossingPairs_mem m v p).mp hp
  have hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 =
          s(some v, none) := by
    exact (Sym2.mem_and_mem_iff (by simp)).mp ⟨hsome, hnone⟩
  exact
    finiteBoundaryGhost_weight_decrement_boundaryGhostCopy
      (β := β) (H := H) m hvbdry hends


theorem finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_zero_of_weight_eq_zero
    {β H : ℝ} {n : ℕ}
    {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v)
    (hweight :
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) =
          0) :
    finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
      β H m v p = 0 := by
  classical
  have hdecrement :=
    finiteBoundaryGhostBoundaryCrossingPairs_weight_decrement
      (β := β) (H := H) m hvbdry hp
  have hprod :
      (β * H) *
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
              (Function.update m p.2.1 (m p.2.1 - 1))) = 0 := by
    rw [hweight, mul_zero] at hdecrement
    exact hdecrement.symm
  unfold finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
  by_cases hsource :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n))
            (Function.update m p.2.1 (m p.2.1 - 1)))
          (copyDeletePreimageDecrementEraseFinset
            (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 p.1) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})
  · simpa [hsource] using hprod
  · simp [hsource]


theorem finiteBoundaryGhostBoundaryCrossingPairs_weight_le_decrement
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
    Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
      ≤
        (β * H) *
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
              (Function.update m p.2.1 (m p.2.1 - 1))) := by
  classical
  let w :=
    Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
  have hw_nonneg : 0 ≤ w := by
    dsimp [w]
    refine
      weight_ofEdgeFun_nonneg_of_nonneg
        (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        hβ ?_ m
    exact boundaryGhostCoupling_nonneg
      (FK.boxBoundary 3 n) hH (fun _ => by norm_num)
  have hmpos : 0 < m p.2.1 :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) p.2.2.2
  have hone_le : (1 : ℝ) ≤ (m p.2.1 : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hmpos
  have hmul_le : w ≤ (m p.2.1 : ℝ) * w := by
    calc
      w = (1 : ℝ) * w := by ring
      _ ≤ (m p.2.1 : ℝ) * w :=
        mul_le_mul_of_nonneg_right hone_le hw_nonneg
  have hdecrement :=
    finiteBoundaryGhostBoundaryCrossingPairs_weight_decrement
      (β := β) (H := H) m hvbdry hp
  exact hmul_le.trans_eq hdecrement


theorem finiteBoundaryGhostBoundaryCrossingPairs_indicator_weight_le_decrement
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
    (if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
      ≤
        (β * H) *
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
              (Function.update m p.2.1 (m p.2.1 - 1))) := by
  classical
  by_cases hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
      finiteBoundaryGhostOnePointSource 3 n
  · rw [if_pos hsrc, one_mul]
    exact finiteBoundaryGhostBoundaryCrossingPairs_weight_le_decrement
      (β := β) (H := H) hβ hH m hvbdry hp
  · rw [if_neg hsrc, zero_mul]
    exact mul_nonneg (mul_nonneg hβ hH)
      (weight_ofEdgeFun_nonneg_of_nonneg
        (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        hβ
        (boundaryGhostCoupling_nonneg
          (FK.boxBoundary 3 n) hH (fun _ => by norm_num))
        (Function.update m p.2.1 (m p.2.1 - 1)))


theorem
    finiteBoundaryGhostBoundaryCrossingPairs_indicator_weight_le_collapsedDecrementDataWeight
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
    (if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
      ≤
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
          (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementData
            m v hsrc hp) := by
  simpa [finiteBoundaryGhostCollapsedTwoPointSourceDataWeight,
    finiteBoundaryGhostTwoPointSourceDataWeight] using
    finiteBoundaryGhostBoundaryCrossingPairs_indicator_weight_le_decrement
      (β := β) (H := H) hβ hH m hvbdry hp


theorem finiteBoundaryGhostBoundaryCrossingPairs_summand_le_decremented_source_summand
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
    (if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
      ≤
        (β * H) *
          ((if Sharpness.RandomCurrent.sources
                (Sharpness.FluxEdgeCopy.endsM
                  (Sharpness.withGhost (FK.boxGraph 3 n))
                  (Function.update m p.2.1 (m p.2.1 - 1)))
                (copyDeletePreimageDecrementEraseFinset
                  (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 p.1) =
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then
              (1 : ℝ)
            else
              0) *
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                (Function.update m p.2.1 (m p.2.1 - 1)))) := by
  classical
  have hsource :=
    finiteBoundaryGhostBoundaryCrossingPairs_decremented_source m v hp
  rw [if_pos hsource, one_mul]
  exact
    finiteBoundaryGhostBoundaryCrossingPairs_indicator_weight_le_decrement
      (β := β) (H := H) hβ hH m hvbdry hp


theorem finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedPairWeightSum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v) :
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤
        ∑ p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
          (β * H) *
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                (Function.update m p.2.1 (m p.2.1 - 1))) := by
  classical
  refine Finset.sum_le_sum ?_
  intro p hp
  exact
    finiteBoundaryGhostBoundaryCrossingPairs_indicator_weight_le_decrement
      (β := β) (H := H) hβ hH m hvbdry hp


theorem
    finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedSourcePairWeightSum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v) :
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤
        ∑ p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
          (β * H) *
            ((if Sharpness.RandomCurrent.sources
                  (Sharpness.FluxEdgeCopy.endsM
                    (Sharpness.withGhost (FK.boxGraph 3 n))
                    (Function.update m p.2.1 (m p.2.1 - 1)))
                  (copyDeletePreimageDecrementEraseFinset
                    (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 p.1) =
                (({some (IsingFK.boxOrigin 3 n)} :
                  Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then
                (1 : ℝ)
              else
                0) *
              Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                  (Function.update m p.2.1 (m p.2.1 - 1)))) := by
  classical
  refine Finset.sum_le_sum ?_
  intro p hp
  exact
    finiteBoundaryGhostBoundaryCrossingPairs_summand_le_decremented_source_summand
      (β := β) (H := H) hβ hH m hvbdry hp


theorem finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedSourceWeightSum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v) :
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤
        Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
          (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
            β H m v) := by
  simpa [finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight]
    using
      finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedSourcePairWeightSum
        (β := β) (H := H) hβ hH m hvbdry


theorem finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementImage_sum_fiber_dataWeight
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v) :
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤
        Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v)
          (fun d =>
            ((finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card :
              ℝ) *
              finiteBoundaryGhostTwoPointSourceDataWeight β H d) := by
  calc
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
        ≤ Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
          (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
            β H m v) :=
      finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedSourceWeightSum
        (β := β) (H := H) hβ hH m hvbdry
    _ =
        Finset.sum
          ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).domain)
          (fun a =>
            finiteBoundaryGhostTwoPointSourceDataWeight β H
              ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).map
                a)) :=
      finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeightSum_eq_indexDomain
        m v
    _ =
        Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v)
          (fun d =>
            ((finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card :
              ℝ) *
              finiteBoundaryGhostTwoPointSourceDataWeight β H d) :=
      finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_dataWeight_indexDomain
        m v


theorem
    finiteBoundaryGhostBoundaryCrossingPairSum_le_collapsedDecrementIndex_sum_fiber_dataWeight
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n) :
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤
        Finset.sum
          (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
            m v hsrc).image
          (fun d =>
            (((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
              m v hsrc).fiber d).card : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
  calc
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤ Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v)
          (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight
            β H m v) :=
      finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedSourceWeightSum
        (β := β) (H := H) hβ hH m hvbdry
    _ =
        Finset.sum
          (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
            m v hsrc).domain
          (fun a =>
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H
              ((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
                m v hsrc).map a)) := by
      rw [← Finset.sum_attach]
      refine Finset.sum_congr rfl ?_
      intro a _ha
      simpa [finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight] using
        (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_dataWeight
          (β := β) (H := H) m (v := v) a.2)
    _ =
        Finset.sum
          (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
            m v hsrc).image
          (fun d =>
            (((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
              m v hsrc).fiber d).card : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) :=
      finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_fiber_dataWeight
        m v hsrc


theorem
    finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_collapsedDecrementImage_sum_dataWeight
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n) :
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          ∑ d ∈ (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
            m v hsrc).image,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
  calc
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤
        Finset.sum
          (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
            m v hsrc).image
          (fun d =>
            (((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
              m v hsrc).fiber d).card : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) :=
      finiteBoundaryGhostBoundaryCrossingPairSum_le_collapsedDecrementIndex_sum_fiber_dataWeight
        (β := β) (H := H) hβ hH m hvbdry hsrc
    _ ≤
        ∑ d ∈ (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
          m v hsrc).image,
          (m ⟨s(some v, none), by
            rw [SimpleGraph.mem_edgeFinset]
            simp [Sharpness.withGhost]⟩ : ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_fiber_weight_le_boundaryGhostMultiplicity_sum
        (β := β) (H := H) hβ hH m v hsrc
    _ =
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          ∑ d ∈ (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
            m v hsrc).image,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
      rw [← Finset.mul_sum]


theorem
    finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_collapsedDataWeight_tsum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n) :
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          ∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
  classical
  have hfinite :=
    finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_collapsedDecrementImage_sum_dataWeight
      (β := β) (H := H) hβ hH m hvbdry hsrc
  have hsum_le :
      (∑ d ∈ (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
        m v hsrc).image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
        ≤
          ∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
    exact
      (finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_summable
        (β := β) (H := H) hβ hH v).sum_le_tsum
        (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex
          m v hsrc).image
        (fun d _hd =>
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_nonneg hβ hH d)
  have hm_nonneg :
      0 ≤ (m ⟨s(some v, none), by
        rw [SimpleGraph.mem_edgeFinset]
        simp [Sharpness.withGhost]⟩ : ℝ) := by
    exact_mod_cast
      Nat.zero_le (m ⟨s(some v, none), by
        rw [SimpleGraph.mem_edgeFinset]
        simp [Sharpness.withGhost]⟩)
  exact hfinite.trans (mul_le_mul_of_nonneg_left hsum_le hm_nonneg)


theorem
    finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n) :
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          ((β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
  have hbound :=
    finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_collapsedDataWeight_tsum
      (β := β) (H := H) hβ hH m hvbdry hsrc
  rw [finiteBoundaryGhostCollapsedDataWeight_tsum_eq_mul_emptyCollapsedSum
    (β := β) (H := H) hβ hH v] at hbound
  exact hbound


theorem
    finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_decrementImage_sum_dataWeight
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v) :
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤
        ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
          (m ⟨s(some v, none), by
            rw [SimpleGraph.mem_edgeFinset]
            simp [Sharpness.withGhost]⟩ : ℝ) *
            finiteBoundaryGhostTwoPointSourceDataWeight β H d := by
  calc
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤
        Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v)
          (fun d =>
            ((finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card :
              ℝ) *
              finiteBoundaryGhostTwoPointSourceDataWeight β H d) :=
      finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementImage_sum_fiber_dataWeight
        (β := β) (H := H) hβ hH m hvbdry
    _ ≤
        ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
          (m ⟨s(some v, none), by
            rw [SimpleGraph.mem_edgeFinset]
            simp [Sharpness.withGhost]⟩ : ℝ) *
            finiteBoundaryGhostTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_weight_le_boundaryGhostMultiplicity_sum
        (β := β) (H := H) hβ hH m v


theorem
    finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v) :
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
            finiteBoundaryGhostTwoPointSourceDataWeight β H d := by
  calc
    (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      ≤
        ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
          (m ⟨s(some v, none), by
            rw [SimpleGraph.mem_edgeFinset]
            simp [Sharpness.withGhost]⟩ : ℝ) *
            finiteBoundaryGhostTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_decrementImage_sum_dataWeight
        (β := β) (H := H) hβ hH m hvbdry
    _ =
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
            finiteBoundaryGhostTwoPointSourceDataWeight β H d := by
      rw [← Finset.mul_sum]


theorem finiteBoundaryGhostSourceSector_subset_boundaryCrossing_biUnion
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (hweight :
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠ 0) :
    finiteBoundaryGhostSourceSector m ⊆
      (Finset.univ.filter (FK.boxBoundary 3 n)).biUnion
        (fun v => finiteBoundaryGhostBoundaryCrossingSourceSector m v) := by
  classical
  intro K hK
  have hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K =
        finiteBoundaryGhostOnePointSource 3 n := by
    simpa [finiteBoundaryGhostSourceSector] using hK
  obtain ⟨v, hvbdry, hcross, _hconn⟩ :=
    finiteBoundaryGhost_sourceSector_has_boundaryGhostCrossingCopy
      (β := β) (H := H) m K hsrc hweight
  rw [Finset.mem_biUnion]
  refine ⟨v, ?_, ?_⟩
  · simp [hvbdry]
  · simpa [finiteBoundaryGhostBoundaryCrossingSourceSector, hK] using hcross


theorem finiteBoundaryGhostSourceSector_card_le_boundaryCrossing_card_sum
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (hweight :
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠ 0) :
    ((finiteBoundaryGhostSourceSector m).card : ℝ) ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ) := by
  classical
  have hnat :
      (finiteBoundaryGhostSourceSector m).card ≤
        ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          (finiteBoundaryGhostBoundaryCrossingSourceSector m v).card := by
    exact
      (Finset.card_le_card
        (finiteBoundaryGhostSourceSector_subset_boundaryCrossing_biUnion
          (β := β) (H := H) m hweight)).trans
        Finset.card_biUnion_le
  exact_mod_cast hnat


theorem finiteBoundaryGhostCollapsedSummand_le_boundaryCrossingSummand_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) :
    ((if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      ((finiteBoundaryGhostSourceSector m).card : ℝ)) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
    ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ((if Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)
              (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
            finiteBoundaryGhostOnePointSource 3 n then
            (1 : ℝ)
          else
            0) *
          ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ)) *
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) := by
  classical
  by_cases hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
      finiteBoundaryGhostOnePointSource 3 n
  · rw [if_pos hsrc]
    let w :=
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
    by_cases hwzero : w = 0
    · simp [w, hwzero]
    · have hw_nonneg : 0 ≤ w := by
        dsimp [w]
        refine
          weight_ofEdgeFun_nonneg_of_nonneg
            (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            hβ ?_ m
        exact boundaryGhostCoupling_nonneg
          (FK.boxBoundary 3 n) hH (fun _ => by norm_num)
      have hcard :=
        finiteBoundaryGhostSourceSector_card_le_boundaryCrossing_card_sum
          (β := β) (H := H) m (by simpa [w] using hwzero)
      calc
        (1 * ((finiteBoundaryGhostSourceSector m).card : ℝ)) * w
            = ((finiteBoundaryGhostSourceSector m).card : ℝ) * w := by ring
        _ ≤
            (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
              ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ)) *
              w :=
          mul_le_mul_of_nonneg_right hcard hw_nonneg
        _ =
            ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
              (1 *
                ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card :
                  ℝ)) * w := by
          rw [Finset.sum_mul]
          simp
  · rw [if_neg hsrc]
    simp


theorem finiteBoundaryGhostBoundaryCrossingSummand_le_crossingPairCountSummand
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    ((if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ)) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
    ≤
      ((if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ)) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) := by
  classical
  by_cases hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
      finiteBoundaryGhostOnePointSource 3 n
  · rw [if_pos hsrc]
    let w :=
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
    have hw_nonneg : 0 ≤ w := by
      dsimp [w]
      refine
        weight_ofEdgeFun_nonneg_of_nonneg
          (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          hβ ?_ m
      exact boundaryGhostCoupling_nonneg
        (FK.boxBoundary 3 n) hH (fun _ => by norm_num)
    have hcard :=
      finiteBoundaryGhostBoundaryCrossingSourceSector_card_le_crossingPairCount
        m v
    calc
      (1 * ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ)) *
          w =
          ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ) *
            w := by ring
      _ ≤ (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ) * w :=
        mul_le_mul_of_nonneg_right hcard hw_nonneg
      _ =
          (1 * (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ)) *
            w := by ring
  · rw [if_neg hsrc]
    simp


theorem finiteBoundaryGhostCollapsedSummand_le_crossingPairCountSummand_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) :
    ((if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      ((finiteBoundaryGhostSourceSector m).card : ℝ)) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
    ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ((if Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)
              (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
            finiteBoundaryGhostOnePointSource 3 n then
            (1 : ℝ)
          else
            0) *
          (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ)) *
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
              m) := by
  classical
  refine
    (finiteBoundaryGhostCollapsedSummand_le_boundaryCrossingSummand_sum
      (β := β) (H := H) hβ hH m).trans ?_
  refine Finset.sum_le_sum ?_
  intro v _hv
  exact
    finiteBoundaryGhostBoundaryCrossingSummand_le_crossingPairCountSummand
      (β := β) (H := H) hβ hH m v


theorem
    finiteBoundaryGhostBoundaryCrossingSummand_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v) :
    ((if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ)) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
    ≤
      (m ⟨s(some v, none), by
        rw [SimpleGraph.mem_edgeFinset]
        simp [Sharpness.withGhost]⟩ : ℝ) *
        ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
          finiteBoundaryGhostTwoPointSourceDataWeight β H d := by
  calc
    ((if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ)) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
      ≤
      ((if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ)) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) :=
      finiteBoundaryGhostBoundaryCrossingSummand_le_crossingPairCountSummand
        (β := β) (H := H) hβ hH m v
    _ =
      ∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
        (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) :=
      finiteBoundaryGhostBoundaryCrossingPairCountSummand_eq_sum_pairs
        (β := β) (H := H) m v
    _ ≤
      (m ⟨s(some v, none), by
        rw [SimpleGraph.mem_edgeFinset]
        simp [Sharpness.withGhost]⟩ : ℝ) *
        ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
          finiteBoundaryGhostTwoPointSourceDataWeight β H d :=
      finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight
        (β := β) (H := H) hβ hH m hvbdry


theorem
    finiteBoundaryGhostBoundaryCrossingSummand_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    (hvbdry : FK.boxBoundary 3 n v) :
    ((if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ)) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
    ≤
      (m ⟨s(some v, none), by
        rw [SimpleGraph.mem_edgeFinset]
        simp [Sharpness.withGhost]⟩ : ℝ) *
        ((β * H) *
          edgeCopySourcePairEmptyCollapsedSum
            (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (({some (IsingFK.boxOrigin 3 n)} :
              Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
  classical
  have hden_nonneg :
      0 ≤
        (β * H) *
          edgeCopySourcePairEmptyCollapsedSum
            (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (({some (IsingFK.boxOrigin 3 n)} :
              Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
    rw [← finiteBoundaryGhostCollapsedDataWeight_tsum_eq_mul_emptyCollapsedSum
      (β := β) (H := H) hβ hH v]
    exact tsum_nonneg
      (fun d =>
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_nonneg hβ hH d)
  have hm_nonneg :
      0 ≤ (m ⟨s(some v, none), by
        rw [SimpleGraph.mem_edgeFinset]
        simp [Sharpness.withGhost]⟩ : ℝ) := by
    exact_mod_cast
      Nat.zero_le (m ⟨s(some v, none), by
        rw [SimpleGraph.mem_edgeFinset]
        simp [Sharpness.withGhost]⟩)
  by_cases hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
      finiteBoundaryGhostOnePointSource 3 n
  · calc
      ((if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ)) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        ≤
        ((if Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)
              (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
            finiteBoundaryGhostOnePointSource 3 n then
            (1 : ℝ)
          else
            0) *
          (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ)) *
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
              m) :=
        finiteBoundaryGhostBoundaryCrossingSummand_le_crossingPairCountSummand
          (β := β) (H := H) hβ hH m v
      _ =
        ∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
          (if Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)
              (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
            finiteBoundaryGhostOnePointSource 3 n then
            (1 : ℝ)
          else
            0) *
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) :=
        finiteBoundaryGhostBoundaryCrossingPairCountSummand_eq_sum_pairs
          (β := β) (H := H) m v
      _ ≤
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          ((β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) :=
        finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum
          (β := β) (H := H) hβ hH m hvbdry hsrc
  · rw [if_neg hsrc]
    simp only [zero_mul]
    exact mul_nonneg hm_nonneg hden_nonneg


theorem
    finiteBoundaryGhostCollapsedSummand_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) :
    ((if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      ((finiteBoundaryGhostSourceSector m).card : ℝ)) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
    ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
            finiteBoundaryGhostTwoPointSourceDataWeight β H d := by
  calc
    ((if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      ((finiteBoundaryGhostSourceSector m).card : ℝ)) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
      ≤
        ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          ((if Sharpness.RandomCurrent.sources
                (Sharpness.FluxEdgeCopy.endsM
                  (Sharpness.withGhost (FK.boxGraph 3 n)) m)
                (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                  (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
              finiteBoundaryGhostOnePointSource 3 n then
              (1 : ℝ)
            else
              0) *
            (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ)) *
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                m) :=
      finiteBoundaryGhostCollapsedSummand_le_crossingPairCountSummand_sum
        (β := β) (H := H) hβ hH m
    _ ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
            finiteBoundaryGhostTwoPointSourceDataWeight β H d := by
      refine Finset.sum_le_sum ?_
      intro v hv
      have hvbdry : FK.boxBoundary 3 n v := by
        exact (Finset.mem_filter.mp hv).2
      calc
        ((if Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)
              (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
            finiteBoundaryGhostOnePointSource 3 n then
            (1 : ℝ)
          else
            0) *
          (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ)) *
          Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
            (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
            (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
              m)
          =
          ∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v,
            (if Sharpness.RandomCurrent.sources
                (Sharpness.FluxEdgeCopy.endsM
                  (Sharpness.withGhost (FK.boxGraph 3 n)) m)
                (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                  (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
              finiteBoundaryGhostOnePointSource 3 n then
              (1 : ℝ)
            else
              0) *
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) :=
          finiteBoundaryGhostBoundaryCrossingPairCountSummand_eq_sum_pairs
            (β := β) (H := H) m v
        _ ≤
          (m ⟨s(some v, none), by
            rw [SimpleGraph.mem_edgeFinset]
            simp [Sharpness.withGhost]⟩ : ℝ) *
            ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v,
              finiteBoundaryGhostTwoPointSourceDataWeight β H d :=
          finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight
            (β := β) (H := H) hβ hH m hvbdry


theorem
    finiteBoundaryGhostCollapsedSummand_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) :
    ((if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      ((finiteBoundaryGhostSourceSector m).card : ℝ)) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
    ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          ((β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
  calc
    ((if Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n then
        (1 : ℝ)
      else
        0) *
      ((finiteBoundaryGhostSourceSector m).card : ℝ)) *
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)
      ≤
        ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          ((if Sharpness.RandomCurrent.sources
                (Sharpness.FluxEdgeCopy.endsM
                  (Sharpness.withGhost (FK.boxGraph 3 n)) m)
                (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                  (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
              finiteBoundaryGhostOnePointSource 3 n then
              (1 : ℝ)
            else
              0) *
            ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card :
              ℝ)) *
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                m) :=
      finiteBoundaryGhostCollapsedSummand_le_boundaryCrossingSummand_sum
        (β := β) (H := H) hβ hH m
    _ ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ : ℝ) *
          ((β * H) *
            edgeCopySourcePairEmptyCollapsedSum
              (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
      refine Finset.sum_le_sum ?_
      intro v hv
      have hvbdry : FK.boxBoundary 3 n v := by
        exact (Finset.mem_filter.mp hv).2
      exact
        finiteBoundaryGhostBoundaryCrossingSummand_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum
          (β := β) (H := H) hβ hH m hvbdry


end Exact3D
end StatMech
