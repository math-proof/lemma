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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part48
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

@[simp] theorem finiteBoundaryGhostBoundaryEdge_coupling
    (H : ℝ) {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : FK.boxBoundary 3 n v) :
    boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
      (finiteBoundaryGhostBoundaryEdge n v).1 = H := by
  simp [finiteBoundaryGhostBoundaryEdge, hv]

set_option maxHeartbeats 800000 in


theorem
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_current_eq_update_target
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (d : finiteBoundaryGhostTwoPointSourceData n v)
    {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d) :
    m =
      Function.update d.1 (finiteBoundaryGhostBoundaryEdge n v)
        (d.1 (finiteBoundaryGhostBoundaryEdge n v) + 1) := by
  classical
  let eGhost := finiteBoundaryGhostBoundaryEdge n v
  have hdata :
      finiteBoundaryGhostBoundaryCrossingPairDecrementData
        (p := p.1) m v p.2 = d :=
    (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_mem
      m v d p).mp hp
  have hedge : p.1.2.1 = eGhost := by
    simpa [eGhost, finiteBoundaryGhostBoundaryEdge] using
      finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_selectedCopy_edge
        m v d hp
  have hdecSelected :
      Function.update m p.1.2.1 (m p.1.2.1 - 1) = d.1 := by
    have hfst :
        (finiteBoundaryGhostBoundaryCrossingPairDecrementData
          (p := p.1) m v p.2).1 = d.1 :=
      congrArg Sigma.fst hdata
    simpa using hfst
  have hdec :
      Function.update m eGhost (m eGhost - 1) = d.1 := by
    simpa [eGhost, hedge] using hdecSelected
  have hmpos_selected : 0 < m p.1.2.1 :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) p.1.2.2.2
  have hmpos : 0 < m eGhost := by
    simpa [hedge] using hmpos_selected
  have hdedge : d.1 eGhost = m eGhost - 1 := by
    have h := congrFun hdec eGhost
    simpa [Function.update_self] using h.symm
  have hmsucc : m eGhost = d.1 eGhost + 1 := by
    rw [hdedge]
    exact (Nat.sub_one_add_one_eq_of_pos hmpos).symm
  funext e
  by_cases he : e = eGhost
  · subst e
    rw [Function.update_self]
    exact hmsucc
  · have hmx : m e = d.1 e := by
      have h := congrFun hdec e
      simpa [Function.update_of_ne he] using h
    rw [Function.update_of_ne he]
    exact hmx


theorem
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_oldBoundaryGhostMultiplicity_eq_succ
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (d : finiteBoundaryGhostTwoPointSourceData n v)
    {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d) :
    m (finiteBoundaryGhostBoundaryEdge n v) =
      d.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 := by
  classical
  have hcurrent :
      m =
        Function.update d.1 (finiteBoundaryGhostBoundaryEdge n v)
          (d.1 (finiteBoundaryGhostBoundaryEdge n v) + 1) :=
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_current_eq_update_target
      m v d hp
  have h := congrFun hcurrent (finiteBoundaryGhostBoundaryEdge n v)
  simpa [Function.update_self] using h


theorem
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_oldBoundaryGhostMultiplicity_le_one_iff_target_zero
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (d : finiteBoundaryGhostTwoPointSourceData n v)
    {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d) :
    m (finiteBoundaryGhostBoundaryEdge n v) ≤ (1 : ℕ) ↔
      d.1 (finiteBoundaryGhostBoundaryEdge n v) = 0 := by
  rw [
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_oldBoundaryGhostMultiplicity_eq_succ
      m v d hp]
  constructor <;> intro h <;> omega


theorem
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_not_oldBoundaryGhostMultiplicity_le_one_iff_target_pos
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (d : finiteBoundaryGhostTwoPointSourceData n v)
    {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d) :
    ¬ m (finiteBoundaryGhostBoundaryEdge n v) ≤ (1 : ℕ) ↔
      0 < d.1 (finiteBoundaryGhostBoundaryEdge n v) := by
  rw [
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_oldBoundaryGhostMultiplicity_eq_succ
      m v d hp]
  constructor <;> intro h <;> omega


theorem
    finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_decrementedBoundaryGhostMultiplicity_succ
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (d : finiteBoundaryGhostTwoPointSourceData n v) :
    (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card ≤
      d.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 := by
  classical
  let eGhost := finiteBoundaryGhostBoundaryEdge n v
  by_cases hempty :
      (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card = 0
  · rw [hempty]
    exact Nat.zero_le _
  · have hnonempty :
        (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).Nonempty := by
      exact Finset.card_pos.mp (Nat.pos_of_ne_zero hempty)
    rcases hnonempty with ⟨p, hp⟩
    have hdata :
        finiteBoundaryGhostBoundaryCrossingPairDecrementData
          (p := p.1) m v p.2 = d :=
      (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_mem
        m v d p).mp hp
    have hedge : p.1.2.1 = eGhost := by
      simpa [eGhost, finiteBoundaryGhostBoundaryEdge] using
        finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_selectedCopy_edge
          m v d hp
    have hmpos_selected : 0 < m p.1.2.1 :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) p.1.2.2.2
    have hmpos : 0 < m eGhost := by
      simpa [hedge] using hmpos_selected
    have hdedge : d.1 eGhost = m eGhost - 1 := by
      have hfst :
          (finiteBoundaryGhostBoundaryCrossingPairDecrementData
            (p := p.1) m v p.2).1 = d.1 :=
        congrArg Sigma.fst hdata
      calc
        d.1 eGhost =
            (Function.update m p.1.2.1 (m p.1.2.1 - 1)) eGhost := by
          exact congrFun hfst.symm eGhost
        _ = m eGhost - 1 := by
          rw [hedge, Function.update_self]
    have hmsucc : m eGhost = d.1 eGhost + 1 := by
      rw [hdedge]
      exact (Nat.sub_one_add_one_eq_of_pos hmpos).symm
    calc
      (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card ≤
          m eGhost := by
        simpa [eGhost, finiteBoundaryGhostBoundaryEdge] using
          finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_boundaryGhostMultiplicity
            m v d
      _ = d.1 eGhost + 1 := hmsucc


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityProfile_mul_currentSum_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (∑ m ∈ Ω,
          (m ⟨s(some v, none), by
            rw [SimpleGraph.mem_edgeFinset]
            simp [Sharpness.withGhost]⟩ : ℝ)) *
          ((β * H) *
            (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
             Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (∅ : Finset (Option (FK.boxVerts 3 n))))) := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m)
      ≤
        ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          (∑ m ∈ Ω,
            (m ⟨s(some v, none), by
              rw [SimpleGraph.mem_edgeFinset]
              simp [Sharpness.withGhost]⟩ : ℝ)) *
            ((β * H) *
              edgeCopySourcePairEmptyCollapsedSum
                (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (({some (IsingFK.boxOrigin 3 n)} :
                  Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) :=
      finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityProfile_mul_emptyCollapsedSum_sum
        (β := β) (H := H) hβ hH Ω
    _ =
        ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          (∑ m ∈ Ω,
            (m ⟨s(some v, none), by
              rw [SimpleGraph.mem_edgeFinset]
              simp [Sharpness.withGhost]⟩ : ℝ)) *
            ((β * H) *
              (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (({some (IsingFK.boxOrigin 3 n)} :
                  Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
               Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (∅ : Finset (Option (FK.boxVerts 3 n))))) := by
      refine Finset.sum_congr rfl ?_
      intro v _hv
      rw [finiteBoundaryGhostCollapsedTwoPointDenominator_eq_currentSum_mul]


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryWeightedProfileCurrentSum_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ∑ m ∈ Ω,
          (m (finiteBoundaryGhostBoundaryEdge n v) : ℝ) *
            ((β *
              boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
                (finiteBoundaryGhostBoundaryEdge n v).1) *
              (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (({some (IsingFK.boxOrigin 3 n)} :
                  Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
               Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (∅ : Finset (Option (FK.boxVerts 3 n))))) := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m)
      ≤
        ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          (∑ m ∈ Ω, (m (finiteBoundaryGhostBoundaryEdge n v) : ℝ)) *
            ((β * H) *
              (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (({some (IsingFK.boxOrigin 3 n)} :
                  Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
               Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
                (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                (∅ : Finset (Option (FK.boxVerts 3 n))))) := by
      simpa [finiteBoundaryGhostBoundaryEdge] using
        finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityProfile_mul_currentSum_sum
          (β := β) (H := H) hβ hH Ω
    _ =
        ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          ∑ m ∈ Ω,
            (m (finiteBoundaryGhostBoundaryEdge n v) : ℝ) *
              ((β *
                boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
                  (finiteBoundaryGhostBoundaryEdge n v).1) *
                (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
                  (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                  (({some (IsingFK.boxOrigin 3 n)} :
                    Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) *
                 Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
                  (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
                  (∅ : Finset (Option (FK.boxVerts 3 n))))) := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
      rw [finiteBoundaryGhostBoundaryEdge_coupling H hvbdry]
      rw [Finset.sum_mul]


end Exact3D
end StatMech
