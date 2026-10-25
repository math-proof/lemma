/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualPair
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


namespace PeriodicPlanarDualPair

variable [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


noncomputable def swap
    (D : PeriodicPlanarDualPair P Pdual) :
    PeriodicPlanarDualPair Pdual P where
  primalEmbedding := D.dualEmbedding
  dualEmbedding := D.primalEmbedding
  coordinates_eq := D.coordinates_eq.symm
  primal_connected := D.dual_connected
  dual_connected := D.primal_connected
  edgeDual := D.edgeDual.symm
  edgeDual_mem_edgeSet := by
    intro e
    simpa using (D.edgeDual_mem_edgeSet (D.edgeDual.symm e)).symm
  edgeDual_shift := by
    intro z e
    apply D.edgeDual.injective
    simpa using (D.edgeDual_shift z (D.edgeDual.symm e)).symm
  edgeDual_crossing := by
    intro x y a b hxy hab hedge
    have hedge' : D.edgeDual s(a, b) = s(x, y) := by
      apply D.edgeDual.symm.injective
      simpa using hedge.symm
    obtain ⟨u, t, hut⟩ := D.edgeDual_crossing hab hxy hedge'
    exact ⟨t, u, hut.symm⟩
  edgeDual_of_crossing := by
    intro x y a b hxy hab t u hcross
    have hedge := D.edgeDual_of_crossing hab hxy u t hcross.symm
    apply D.edgeDual.injective
    simpa using hedge.symm
  free_wired_infiniteVolume_dual_law := by
    intro p q hp hp1 hq
    have hq0 : 0 < q := zero_lt_one.trans_le hq
    have hpStar := dualParam_mem_Ioo hp hp1 hq0
    have hinv := dualParam_involutive hp hp1 hq0
    have h := D.wired_free_infiniteVolume_dual_law
      hpStar.1 hpStar.2 hq
    have h' :
        Pdual.freeBufferedInfiniteVolume hp hp1 hq0 =
          (P.wiredBufferedInfiniteVolume hpStar.1 hpStar.2 hq0).map
            (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable := by
      simpa only [hinv] using h
    apply ProbabilityMeasure.toMeasure_injective
    change _ = Measure.map _ _
    rw [h', ProbabilityMeasure.toMeasure_map, Measure.map_map]
    · simpa [dualConfigEquiv_symm]
    · exact (continuous_dualConfigEquiv D.edgeDual.symm).measurable
    · exact (continuous_dualConfigEquiv D.edgeDual).measurable
  wired_free_infiniteVolume_dual_law := by
    intro p q hp hp1 hq
    have hq0 : 0 < q := zero_lt_one.trans_le hq
    have hpStar := dualParam_mem_Ioo hp hp1 hq0
    have hinv := dualParam_involutive hp hp1 hq0
    have h := D.free_wired_infiniteVolume_dual_law
      hpStar.1 hpStar.2 hq
    have h' :
        Pdual.wiredBufferedInfiniteVolume hp hp1 hq0 =
          (P.freeBufferedInfiniteVolume hpStar.1 hpStar.2 hq0).map
            (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable := by
      simpa only [hinv] using h
    apply ProbabilityMeasure.toMeasure_injective
    change _ = Measure.map _ _
    rw [h', ProbabilityMeasure.toMeasure_map, Measure.map_map]
    · simpa [dualConfigEquiv_symm]
    · exact (continuous_dualConfigEquiv D.edgeDual.symm).measurable
    · exact (continuous_dualConfigEquiv D.edgeDual).measurable

end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
