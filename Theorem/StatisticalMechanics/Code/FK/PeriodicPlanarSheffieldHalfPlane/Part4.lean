/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part23
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlane.Part4
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicPlaneEmbedding.halfPlanePairMergeError_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : ℝ) (x y : V) :
    MeasurableSet (E.halfPlanePairMergeError r x y) :=
  ((P.measurableSet_cluster_infinite x).inter
    (P.measurableSet_cluster_infinite y)).diff
      (P.connectedWithinSet_measurableSet (E.rightHalfPlaneVertices r) x y)


theorem PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_preimage_subset
    (E : PeriodicPlaneEmbedding P) (N : ℕ) (r : ℝ) (x y : V) :
    ∃ z : Site 2,
      P.configTranslate z ⁻¹'
          E.halfPlanePairMergeError r (P.shift z x) (P.shift z y) ⊆
        P.pairMergeError x y N := by
  obtain ⟨z, htransport⟩ :=
    E.exists_shift_connectedWithinOrbit_into_rightHalfPlane N r
  refine ⟨z, ?_⟩
  intro omega herror
  change P.configTranslate z omega ∈
    E.halfPlanePairMergeError r (P.shift z x) (P.shift z y) at herror
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (P.cluster_infinite_configTranslate z omega x).mp herror.1.1
  · exact (P.cluster_infinite_configTranslate z omega y).mp herror.1.2
  · intro hmerge
    exact herror.2 (htransport omega x y hmerge)


theorem PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (N : ℕ) (r : ℝ) (x y : V) :
    ∃ z : Site 2,
      mu.real (E.halfPlanePairMergeError r (P.shift z x) (P.shift z y)) ≤
        mu.real (P.pairMergeError x y N) := by
  obtain ⟨z, hsub⟩ :=
    E.exists_shift_halfPlanePairMergeError_preimage_subset N r x y
  refine ⟨z, ?_⟩
  have hmeasure := P.translateEvent_measure_eq mu hTI z
    (E.halfPlanePairMergeError_measurableSet r (P.shift z x) (P.shift z y))
  have hreal :
      mu.real (P.configTranslate z ⁻¹'
        E.halfPlanePairMergeError r (P.shift z x) (P.shift z y)) =
      mu.real (E.halfPlanePairMergeError r (P.shift z x) (P.shift z y)) :=
    congrArg ENNReal.toReal hmeasure
  rw [← hreal]
  exact measureReal_mono hsub


theorem PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_measureReal_lt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : ℝ) (x y : V) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : Site 2,
      mu.real (E.halfPlanePairMergeError r (P.shift z x) (P.shift z y)) < ε := by
  have ht := P.pairMergeError_real_tendsto_zero mu hunique x y
  have hev : ∀ᶠ N in atTop, mu.real (P.pairMergeError x y N) < ε :=
    (tendsto_order.1 ht).2 ε hε
  obtain ⟨N, hN⟩ := hev.exists
  obtain ⟨z, hz⟩ :=
    E.exists_shift_halfPlanePairMergeError_measureReal_le mu hTI N r x y
  exact ⟨z, hz.trans_lt hN⟩

end StatMech.FK.PeriodicPlanar
