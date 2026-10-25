/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarDualPair.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


namespace PeriodicPlanarDualPair

variable [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem wiredPercolationProbability_dualParam
    (D : PeriodicPlanarDualPair P Pdual) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Pdual.wiredPercolationProbability (dualParam p q) q =
      D.freeDualPercolationProbability p q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpDual := dualParam_mem_Ioo hp hp1 hq0
  unfold PeriodicGraph.wiredPercolationProbability
    freeDualPercolationProbability
  rw [dif_pos ⟨hpDual, hq0⟩, dif_pos ⟨⟨hp, hp1⟩, hq0⟩]
  exact congrArg ENNReal.toReal (D.wiredDual_percolationEvent hp hp1 hq)


theorem wiredPercolates_dualParam_iff
    (D : PeriodicPlanarDualPair P Pdual) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Pdual.wiredPercolates (dualParam p q) q ↔
      D.FreeDualPercolates p q := by
  unfold PeriodicGraph.wiredPercolates FreeDualPercolates
  rw [D.wiredPercolationProbability_dualParam hp hp1 hq]


theorem dualSubcriticalCoverage_iff_freeDual
    (D : PeriodicPlanarDualPair P Pdual) {pc q : ℝ} (hq : 1 ≤ q) :
    DualSubcriticalCoverage
        (fun r => Pdual.wiredPercolates r q) pc q ↔
      ∀ p ∈ Ioo (0 : ℝ) 1, p < pc → D.FreeDualPercolates p q := by
  constructor
  · intro h p hp hpc
    exact (D.wiredPercolates_dualParam_iff hp.1 hp.2 hq).mp
      (h p hp hpc)
  · intro h p hp hpc
    exact (D.wiredPercolates_dualParam_iff hp.1 hp.2 hq).mpr
      (h p hp hpc)


theorem dualNoCoexistence_iff_freeDual
    (D : PeriodicPlanarDualPair P Pdual) {q : ℝ} (hq : 1 ≤ q) :
    DualNoCoexistence
        (fun p => P.wiredPercolates p q)
        (fun r => Pdual.wiredPercolates r q) q ↔
      ∀ p ∈ Ioo (0 : ℝ) 1,
        ¬(P.wiredPercolates p q ∧ D.FreeDualPercolates p q) := by
  constructor
  · intro h p hp
    simpa only [D.wiredPercolates_dualParam_iff hp.1 hp.2 hq] using h p hp
  · intro h p hp
    simpa only [D.wiredPercolates_dualParam_iff hp.1 hp.2 hq] using h p hp


theorem dualCritical_relation_of_commonCoupling
    (D : PeriodicPlanarDualPair P Pdual) {q : ℝ}
    (hpc : P.criticalPoint q ∈ Ioo (0 : ℝ) 1)
    (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : ℝ) 1)
    (hq : 1 ≤ q)
    (hcoverage : ∀ p ∈ Ioo (0 : ℝ) 1,
      p < P.criticalPoint q → D.FreeDualPercolates p q)
    (hnoCoexistence : ∀ p ∈ Ioo (0 : ℝ) 1,
      ¬(P.wiredPercolates p q ∧ D.FreeDualPercolates p q)) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  apply P.dualCritical_relation_of_noCoexistence Pdual
    hpc hpcDual hq
  · exact (D.dualSubcriticalCoverage_iff_freeDual hq).mpr hcoverage
  · exact (D.dualNoCoexistence_iff_freeDual hq).mpr hnoCoexistence

end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
