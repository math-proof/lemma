/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualBurtonKeane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneUniqueness
open MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicGraph.hasInfiniteCluster_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    P.HasInfiniteCluster (P.configTranslate z omega) ↔
      P.HasInfiniteCluster omega := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨P.shift (-z) x, ?_⟩
    exact (P.cluster_infinite_configTranslate z omega
      (P.shift (-z) x)).mp (by simpa using hx)
  · rintro ⟨x, hx⟩
    exact ⟨P.shift z x, (P.cluster_infinite_configTranslate z omega x).2 hx⟩


theorem PeriodicGraph.hasInfiniteCluster_measure_eq_one_of_percolation_pos
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (herg : P.IsErgodic mu)
    (hpos : 0 < mu P.percolationEvent) :
    mu {omega | P.HasInfiniteCluster omega} = 1 := by
  have hinv : ∀ z : Site 2,
      P.configTranslate z ⁻¹' {omega | P.HasInfiniteCluster omega} =
        {omega | P.HasInfiniteCluster omega} := by
    intro z
    ext omega
    exact P.hasInfiniteCluster_configTranslate z omega
  have hsub : P.percolationEvent ⊆
      {omega | P.HasInfiniteCluster omega} := by
    intro omega hroot
    exact ⟨P.root, hroot⟩
  have hhasPos : 0 < mu {omega | P.HasInfiniteCluster omega} :=
    hpos.trans_le (measure_mono hsub)
  rcases herg.2 _ P.measurableSet_hasInfiniteCluster hinv with hzero | hone
  · rw [hzero] at hhasPos
    exact False.elim (lt_irrefl 0 hhasPos)
  · exact hone


theorem PeriodicGraph.hasUniqueInfiniteCluster_measure_eq_one_of_zero_or_one
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hzeroOne : ∃ k : ℕ∞,
      mu {omega | P.numInfiniteClusters omega = k} = 1 ∧
        (k = 0 ∨ k = 1))
    (hinfinite : mu {omega | P.HasInfiniteCluster omega} = 1) :
    mu {omega | P.HasUniqueInfiniteCluster omega} = 1 := by
  obtain ⟨k, hk, hk0 | hk1⟩ := hzeroOne
  · subst k
    have hcomp : mu {omega | P.HasInfiniteCluster omega}ᶜ = 0 :=
      (prob_compl_eq_zero_iff P.measurableSet_hasInfiniteCluster).2 hinfinite
    have hsub : {omega | P.numInfiniteClusters omega = 0} ⊆
        {omega | P.HasInfiniteCluster omega}ᶜ := by
      intro omega hzero hinf
      obtain ⟨x, hx⟩ := hinf
      have hnonempty : (P.infiniteClusters omega).Nonempty :=
        ⟨P.cluster omega x, hx, x, rfl⟩
      have hne : (P.infiniteClusters omega).encard ≠ 0 :=
        Set.encard_ne_zero.mpr hnonempty
      exact hne (by simpa [PeriodicGraph.numInfiniteClusters] using hzero)
    have hzero := measure_mono_null hsub hcomp
    rw [hk] at hzero
    exact False.elim (one_ne_zero hzero)
  · subst k
    rwa [P.numInfiniteClusters_eq_one_event] at hk


theorem PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_hasUniqueInfiniteCluster_measure_eq_one
    (E : PeriodicPlaneEmbedding P) (hconn : P.graph.Connected)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hperc : 0 <
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        P.percolationEvent) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _)
      {omega | P.HasUniqueInfiniteCluster omega} = 1 := by
  let mu := (P.freeBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
  have herg := E.freeBufferedInfiniteVolume_isErgodic hp hp1 hq
  have hpercMeasure : 0 < mu P.percolationEvent :=
    (ENNReal.toReal_pos_iff.mp hperc).1
  have hinfinite := P.hasInfiniteCluster_measure_eq_one_of_percolation_pos
    mu herg hpercMeasure
  exact P.hasUniqueInfiniteCluster_measure_eq_one_of_zero_or_one mu
    (E.freeBufferedInfiniteVolume_numInfiniteClusters_zero_or_one
      hconn hp hp1 hq) hinfinite

end StatMech.FK.PeriodicPlanar
