/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part9
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

variable [Countable V]


omit [Countable V] in
theorem PeriodicGraph.bufferedCylinder_isClopen
    (P : PeriodicGraph V) (N : ℕ)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    IsClopen (P.bufferedCylinder N S) :=
  IsClopen.preimage ⟨isClosed_discrete _, isOpen_discrete _⟩
    (P.continuous_bufferedRestrict N)

theorem PeriodicGraph.bufferedCylinder_measurableSet
    (P : PeriodicGraph V) (N : ℕ)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    MeasurableSet (P.bufferedCylinder N S) :=
  (P.bufferedCylinder_isClopen N S).isOpen.measurableSet

omit [Countable V] in
theorem PeriodicGraph.bufferedCylinder_isIncreasing
    (P : PeriodicGraph V) (N : ℕ)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    IsIncreasing (P.bufferedCylinder N S) :=
  fun _ _ home hmem => hS (P.monotone_bufferedRestrict N home) hmem

theorem fkPMF_toMeasure_toReal_generic
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 W))) :
    ((fkPMF G hp hp1 hq).toMeasure S).toReal =
      ∑ omega, S.indicator (fun _ => (1 : ℝ)) omega * fkProb G p q omega := by
  classical
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun a _ => ?_)]
  · apply Finset.sum_congr rfl
    intro omega _
    by_cases homega : omega ∈ S
    · rw [Set.indicator_of_mem homega, Set.indicator_of_mem homega,
        fkPMF_apply, ENNReal.toReal_ofReal (fkProb_nonneg G hp hp1 hq omega), one_mul]
    · rw [Set.indicator_of_notMem homega, Set.indicator_of_notMem homega]
      simp
  · by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha, fkPMF_apply]
      exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem ha]
      simp

theorem wiredFkPMF_toMeasure_toReal_generic
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (bdry : W → Prop) [DecidablePred bdry]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 W))) :
    ((wiredFkPMF G bdry hp hp1 hq).toMeasure S).toReal =
      ∑ omega, S.indicator (fun _ => (1 : ℝ)) omega *
        wiredFkProb G bdry p q omega := by
  classical
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun a _ => ?_)]
  · apply Finset.sum_congr rfl
    intro omega _
    by_cases homega : omega ∈ S
    · rw [Set.indicator_of_mem homega, Set.indicator_of_mem homega,
        wiredFkPMF, PMF.ofFintype_apply,
        ENNReal.toReal_ofReal (wiredFkProb_nonneg G bdry hp hp1 hq omega), one_mul]
    · rw [Set.indicator_of_notMem homega, Set.indicator_of_notMem homega]
      simp
  · by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha, wiredFkPMF, PMF.ofFintype_apply]
      exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem ha]
      simp

theorem PeriodicGraph.freeBufferedMeasure_real_cylinder
    (P : PeriodicGraph V) {N m : ℕ} (hNm : N ≤ m)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    (P.freeBufferedMeasure m hp hp1 hq : Measure (ConfigSpace (Sym2 V))).real
        (P.bufferedCylinder N S) =
      ∑ omega,
        (P.bufferedRestrictLE hNm ⁻¹' S).indicator (fun _ => (1 : ℝ)) omega *
          fkProb (P.bufferedGraph m) p q omega := by
  have hmap : (P.freeBufferedMeasure m hp hp1 hq : Measure _).real
        (P.bufferedCylinder N S) =
      ((fkPMF (P.bufferedGraph m) hp hp1 hq).toMeasure
        (P.extendEdge (P.bufferedRadius m) ⁻¹' P.bufferedCylinder N S)).toReal := by
    unfold PeriodicGraph.freeBufferedMeasure PeriodicGraph.freeFiniteMeasure
      PeriodicGraph.freeFinitePMF PeriodicGraph.bufferedGraph Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (P.measurable_extendEdge (P.bufferedRadius m))
      (P.bufferedCylinder_measurableSet N S)]
    rfl
  have hpre : P.extendEdge (P.bufferedRadius m) ⁻¹' P.bufferedCylinder N S =
      P.bufferedRestrictLE hNm ⁻¹' S := by
    ext omega
    simp only [PeriodicGraph.bufferedCylinder, Set.mem_preimage,
      P.bufferedRestrict_extendEdge_le hNm]
  rw [hmap, hpre]
  exact fkPMF_toMeasure_toReal_generic (P.bufferedGraph m) hp hp1 hq _

theorem PeriodicGraph.wiredBufferedMeasure_real_cylinder
    (P : PeriodicGraph V) {N m : ℕ} (hNm : N ≤ m)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    (P.wiredBufferedMeasure m hp hp1 hq : Measure (ConfigSpace (Sym2 V))).real
        (P.bufferedCylinder N S) =
      ∑ omega,
        (P.bufferedRestrictLE hNm ⁻¹' S).indicator (fun _ => (1 : ℝ)) omega *
          wiredFkProb (P.bufferedGraph m) (P.bufferedBoundary m) p q omega := by
  have hmap : (P.wiredBufferedMeasure m hp hp1 hq : Measure _).real
        (P.bufferedCylinder N S) =
      ((P.wiredBufferedPMF m hp hp1 hq).toMeasure
        (P.extendEdge (P.bufferedRadius m) ⁻¹' P.bufferedCylinder N S)).toReal := by
    unfold PeriodicGraph.wiredBufferedMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (P.measurable_extendEdge (P.bufferedRadius m))
      (P.bufferedCylinder_measurableSet N S)]
  have hpre : P.extendEdge (P.bufferedRadius m) ⁻¹' P.bufferedCylinder N S =
      P.bufferedRestrictLE hNm ⁻¹' S := by
    ext omega
    simp only [PeriodicGraph.bufferedCylinder, Set.mem_preimage,
      P.bufferedRestrict_extendEdge_le hNm]
  rw [hmap, hpre]
  exact wiredFkPMF_toMeasure_toReal_generic (P.bufferedGraph m)
    (P.bufferedBoundary m) hp hp1 hq _

theorem PeriodicGraph.freeBufferedMeasure_step_cylinder
    (P : PeriodicGraph V) {N m : ℕ} (hNm : N ≤ m)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) ≤
      (P.freeBufferedMeasure (m + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) := by
  rw [P.freeBufferedMeasure_real_cylinder hNm hp hp1 (zero_lt_one.trans_le hq),
    P.freeBufferedMeasure_real_cylinder (hNm.trans (Nat.le_succ m))
      hp hp1 (zero_lt_one.trans_le hq)]
  let A := P.bufferedRestrictLE hNm ⁻¹' S
  have hA : IsIncreasing A := fun _ _ home hmem =>
    hS (P.monotone_bufferedRestrictLE hNm home) hmem
  have hstep := P.freeBuffered_step m hp hp1 hq hA
  have hpre : ocd_innerRestrict (P.bufferedVertexIncl m) ⁻¹' A =
      P.bufferedRestrictLE (hNm.trans (Nat.le_succ m)) ⁻¹' S := by
    ext omega
    simp only [A, Set.mem_preimage, P.bufferedRestrictLE_succ hNm]
  rwa [hpre] at hstep

theorem PeriodicGraph.wiredBufferedMeasure_step_cylinder
    (P : PeriodicGraph V) {N m : ℕ} (hNm : N ≤ m)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (P.wiredBufferedMeasure (m + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) ≤
      (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) := by
  rw [P.wiredBufferedMeasure_real_cylinder (hNm.trans (Nat.le_succ m))
      hp hp1 (zero_lt_one.trans_le hq),
    P.wiredBufferedMeasure_real_cylinder hNm hp hp1 (zero_lt_one.trans_le hq)]
  let A := P.bufferedRestrictLE hNm ⁻¹' S
  have hA : IsIncreasing A := fun _ _ home hmem =>
    hS (P.monotone_bufferedRestrictLE hNm home) hmem
  have hstep := P.wiredBuffered_step m hp hp1 hq hA
  have hpre : ocd_innerRestrict (P.bufferedVertexIncl m) ⁻¹' A =
      P.bufferedRestrictLE (hNm.trans (Nat.le_succ m)) ⁻¹' S := by
    ext omega
    simp only [A, Set.mem_preimage, P.bufferedRestrictLE_succ hNm]
  rwa [hpre] at hstep


end PeriodicPlanar
end FK
end StatMech
