/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarThermodynamicDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part12
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarThermodynamicDuality.Part2
open MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {E F : Type*}


@[simp] theorem dualConfigEquiv_symm (edgeDual : E ≃ F) :
    dualConfigEquiv edgeDual.symm = (dualConfigEquiv edgeDual).symm := by
  ext eta e
  rfl

variable [Countable E] [Countable F]


theorem weakLimit_dual_of_finite_exchange
    (edgeDual : E ≃ F)
    (mu : ℕ → ProbabilityMeasure (ConfigSpace E))
    (muDual : ℕ → ProbabilityMeasure (ConfigSpace F))
    (nu : ProbabilityMeasure (ConfigSpace E))
    (nuDual : ProbabilityMeasure (ConfigSpace F))
    (hfinite : ∀ n, muDual n =
      (mu n).map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable)
    (hmu : WeakConvergesTo mu nu)
    (hdual : WeakConvergesTo muDual nuDual) :
    nuDual = nu.map
      (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable := by
  have hmapped : WeakConvergesTo
      (fun n => (mu n).map
        (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable)
      (nu.map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      mu nu hmu (continuous_dualConfigEquiv edgeDual)
  have hseq : (fun n => (mu n).map
      (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable) = muDual := by
    funext n
    exact (hfinite n).symm
  rw [hseq] at hmapped
  exact tendsto_nhds_unique hdual hmapped


theorem weakLimit_dual_event
    (edgeDual : E ≃ F)
    (nu : ProbabilityMeasure (ConfigSpace E))
    (nuDual : ProbabilityMeasure (ConfigSpace F))
    (hdual : nuDual = nu.map
      (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable)
    {A : Set (ConfigSpace F)} (hA : MeasurableSet A) :
    (nuDual : Measure (ConfigSpace F)) A =
      (nu : Measure (ConfigSpace E)) ((dualConfigEquiv edgeDual) ⁻¹' A) := by
  rw [hdual, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (continuous_dualConfigEquiv edgeDual).measurable hA]


theorem weakLimit_dual_of_subsequence_exchange
    (edgeDual : E ≃ F)
    (mu : ℕ → ProbabilityMeasure (ConfigSpace E))
    (muDual : ℕ → ProbabilityMeasure (ConfigSpace F))
    (phi : ℕ → ℕ)
    (nu : ProbabilityMeasure (ConfigSpace E))
    (nuDual : ProbabilityMeasure (ConfigSpace F))
    (hfinite : ∀ n, muDual n =
      (mu n).map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable)
    (hmu : WeakConvergesTo (fun n => mu (phi n)) nu)
    (hdual : WeakConvergesTo (fun n => muDual (phi n)) nuDual) :
    nuDual = nu.map
      (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable := by
  apply weakLimit_dual_of_finite_exchange edgeDual
    (fun n => mu (phi n)) (fun n => muDual (phi n)) nu nuDual
  · exact fun n => hfinite (phi n)
  · exact hmu
  · exact hdual


theorem exists_common_weak_dual_limits
    (edgeDual : E ≃ F)
    (mu : ℕ → ProbabilityMeasure (ConfigSpace E))
    (muDual : ℕ → ProbabilityMeasure (ConfigSpace F))
    (hfinite : ∀ n, muDual n =
      (mu n).map (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable) :
    ∃ (phi : ℕ → ℕ)
      (nu : ProbabilityMeasure (ConfigSpace E))
      (nuDual : ProbabilityMeasure (ConfigSpace F)),
      StrictMono phi ∧
      WeakConvergesTo (fun n => mu (phi n)) nu ∧
      WeakConvergesTo (fun n => muDual (phi n)) nuDual ∧
      nuDual = nu.map
        (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable := by
  obtain ⟨nu, phi, hphi, hmu⟩ := prokhorov_seq_compact mu
  let nuDual := nu.map
    (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable
  have hmapped : WeakConvergesTo
      (fun n => (mu (phi n)).map
        (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable)
      nuDual :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => mu (phi n)) nu hmu (continuous_dualConfigEquiv edgeDual)
  have hseq : (fun n => (mu (phi n)).map
      (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable) =
      (fun n => muDual (phi n)) := by
    funext n
    exact (hfinite (phi n)).symm
  rw [hseq] at hmapped
  exact ⟨phi, nu, nuDual, hphi, hmu, hmapped, rfl⟩


variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]


theorem PeriodicGraph.free_wired_bufferedInfiniteVolume_dual
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W)
    (edgeDual : Sym2 V ≃ Sym2 W)
    {p pDual q qDual : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hpDual : 0 < pDual) (hpDual1 : pDual < 1) (hqDual : 1 ≤ qDual)
    (hfinite : ∀ n,
      Pdual.wiredBufferedMeasure n hpDual hpDual1 (zero_lt_one.trans_le hqDual) =
        (P.freeBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq)).map
          (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable) :
    Pdual.wiredBufferedInfiniteVolume hpDual hpDual1
        (zero_lt_one.trans_le hqDual) =
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)).map
        (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable := by
  exact weakLimit_dual_of_finite_exchange edgeDual
    (fun n => P.freeBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq))
    (fun n => Pdual.wiredBufferedMeasure n hpDual hpDual1
      (zero_lt_one.trans_le hqDual))
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq))
    (Pdual.wiredBufferedInfiniteVolume hpDual hpDual1
      (zero_lt_one.trans_le hqDual))
    hfinite
    (P.freeBufferedMeasure_weakConverges hp hp1 hq)
    (Pdual.wiredBufferedMeasure_weakConverges hpDual hpDual1 hqDual)


theorem PeriodicGraph.wired_free_bufferedInfiniteVolume_dual
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W)
    (edgeDual : Sym2 V ≃ Sym2 W)
    {p pDual q qDual : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hpDual : 0 < pDual) (hpDual1 : pDual < 1) (hqDual : 1 ≤ qDual)
    (hfinite : ∀ n,
      Pdual.freeBufferedMeasure n hpDual hpDual1 (zero_lt_one.trans_le hqDual) =
        (P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq)).map
          (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable) :
    Pdual.freeBufferedInfiniteVolume hpDual hpDual1
        (zero_lt_one.trans_le hqDual) =
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)).map
        (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable := by
  exact weakLimit_dual_of_finite_exchange edgeDual
    (fun n => P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq))
    (fun n => Pdual.freeBufferedMeasure n hpDual hpDual1
      (zero_lt_one.trans_le hqDual))
    (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq))
    (Pdual.freeBufferedInfiniteVolume hpDual hpDual1
      (zero_lt_one.trans_le hqDual))
    hfinite
    (P.wiredBufferedMeasure_weakConverges hp hp1 hq)
    (Pdual.freeBufferedMeasure_weakConverges hpDual hpDual1 hqDual)

end PeriodicPlanar
end FK
end StatMech
