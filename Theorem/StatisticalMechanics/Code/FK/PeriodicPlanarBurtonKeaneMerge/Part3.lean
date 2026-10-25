/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneCore.Part3
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneMerge.Part2
open MeasureTheory Set SimpleGraph
open scoped ENNReal


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [Countable V] [DecidableEq V]

theorem PeriodicGraph.exists_distinctInfinitePair_of_two_le
    (P : PeriodicGraph V) {omega : ConfigSpace (Sym2 V)}
    (h : 2 <= P.numInfiniteClusters omega) :
    ∃ x y, omega ∈ P.distinctInfinitePairEvent x y := by
  have hone : 1 < (P.infiniteClusters omega).encard := by
    change 2 <= (P.infiniteClusters omega).encard at h
    exact lt_of_lt_of_le (by norm_num) h
  obtain ⟨Cx, Cy, hCx, hCy, hne⟩ := Set.one_lt_encard_iff.mp hone
  obtain ⟨hxInf, x, rfl⟩ := hCx
  obtain ⟨hyInf, y, rfl⟩ := hCy
  exact ⟨x, y, hxInf, hyInf, hne⟩

theorem PeriodicGraph.exists_distinctInfinitePair_pos
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] {k : ℕ∞}
    (hk : mu {omega | P.numInfiniteClusters omega = k} = 1)
    (hk2 : 2 <= k) :
    ∃ x y, 0 < mu (P.distinctInfinitePairEvent x y) := by
  by_contra h
  push Not at h
  have hzero : ∀ x y, mu (P.distinctInfinitePairEvent x y) = 0 := by
    intro x y
    exact le_antisymm (h x y) bot_le
  have hunion0 : mu (⋃ x, ⋃ y, P.distinctInfinitePairEvent x y) = 0 :=
    measure_iUnion_null fun x => measure_iUnion_null (hzero x)
  have hsub : {omega | P.numInfiniteClusters omega = k} ⊆
      ⋃ x, ⋃ y, P.distinctInfinitePairEvent x y := by
    intro omega homega
    obtain ⟨x, y, hxy⟩ := P.exists_distinctInfinitePair_of_two_le
      (show 2 <= P.numInfiniteClusters omega from homega.symm ▸ hk2)
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨y, hxy⟩⟩
  have hone : (1 : ENNReal) <= mu (⋃ x, ⋃ y, P.distinctInfinitePairEvent x y) := by
    rw [← hk]
    exact measure_mono hsub
  rw [hunion0] at hone
  exact one_ne_zero (le_antisymm hone bot_le)

theorem PeriodicGraph.exists_forceOpen_walk
    (P : PeriodicGraph V) (hconn : P.graph.Connected) (x y : V) :
    ∃ F : Finset (Sym2 V), ∀ omega,
      (P.openSubgraph (forceOpenFinset F omega)).Reachable x y := by
  obtain ⟨w⟩ := hconn.preconnected x y
  let F : Finset (Sym2 V) := w.edges.toFinset
  refine ⟨F, fun omega => ⟨w.transfer (P.openSubgraph (forceOpenFinset F omega)) ?_⟩⟩
  intro e he
  have heG := w.edges_subset_edgeSet he
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at heG ⊢
      rw [P.openSubgraph_adj]
      refine ⟨heG, ?_⟩
      exact forceOpenFinset_of_mem (by simpa [F] using he) omega

theorem PeriodicGraph.measurableSet_numInfiniteClusters_lt
    (P : PeriodicGraph V) (k : ℕ∞) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      P.numInfiniteClusters omega < k} :=
  P.measurable_numInfiniteClusters MeasurableSet.of_discrete

theorem PeriodicGraph.numInfiniteClusters_lt_null
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] {k : ℕ∞}
    (hk : mu {omega | P.numInfiniteClusters omega = k} = 1) :
    mu {omega | P.numInfiniteClusters omega < k} = 0 := by
  have hsub : {omega | P.numInfiniteClusters omega = k} ⊆
      {omega | P.numInfiniteClusters omega < k}ᶜ := by
    intro omega homega
    simp only [Set.mem_setOf_eq] at homega
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, homega]
    exact lt_irrefl k
  have hfull : mu {omega | P.numInfiniteClusters omega < k}ᶜ = 1 :=
    le_antisymm prob_le_one (hk ▸ measure_mono hsub)
  exact (prob_compl_eq_one_iff (P.measurableSet_numInfiniteClusters_lt k)).mp hfull


theorem PeriodicGraph.numInfiniteClusters_const_ne_finite_two
    (P : PeriodicGraph V) (hconn : P.graph.Connected)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hfe : HasFiniteEnergy mu) {k : ℕ∞}
    (hk : mu {omega | P.numInfiniteClusters omega = k} = 1)
    (hk2 : 2 <= k) (hktop : k ≠ ⊤) : False := by
  obtain ⟨x, y, hpairPos⟩ := P.exists_distinctInfinitePair_pos mu hk hk2
  obtain ⟨F, hF⟩ := P.exists_forceOpen_walk hconn x y
  let K := {omega : ConfigSpace (Sym2 V) |
    P.numInfiniteClusters omega = k}
  let A := P.distinctInfinitePairEvent x y ∩ K
  let B := {omega : ConfigSpace (Sym2 V) |
    P.numInfiniteClusters omega < k}
  have hKmeas : MeasurableSet K :=
    P.measurable_numInfiniteClusters (measurableSet_singleton k)
  have hKcompl : mu Kᶜ = 0 := (prob_compl_eq_zero_iff hKmeas).2 hk
  have hApos : 0 < mu A := by
    by_contra hnot
    have hA0 : mu A = 0 := le_antisymm (not_lt.mp hnot) bot_le
    have hpairSub : P.distinctInfinitePairEvent x y ⊆ A ∪ Kᶜ := by
      intro omega homega
      by_cases hK : omega ∈ K
      · exact Or.inl ⟨homega, hK⟩
      · exact Or.inr hK
    have hpair0 : mu (P.distinctInfinitePairEvent x y) = 0 :=
      measure_mono_null hpairSub (measure_union_null hA0 hKcompl)
    rw [hpair0] at hpairPos
    exact (lt_irrefl 0) hpairPos
  have hsub : A ⊆ forceOpenFinset F ⁻¹' B := by
    intro omega homega
    have hcount : P.numInfiniteClusters omega = k := homega.2
    have hfinite : P.numInfiniteClusters omega ≠ ⊤ := by
      rw [hcount]
      exact hktop
    have hlt := P.numInfiniteClusters_lt_of_merge F omega hfinite x y
      homega.1.1 homega.1.2.1 homega.1.2.2 (hF omega)
    change P.numInfiniteClusters (forceOpenFinset F omega) < k
    rwa [hcount] at hlt
  have hnull := P.numInfiniteClusters_lt_null mu hk
  have hpush : (mu.map (forceOpenFinset F)) B = mu (forceOpenFinset F ⁻¹' B) :=
    Measure.map_apply (measurable_forceOpenFinset F)
      (P.measurableSet_numInfiniteClusters_lt k)
  have hpre0 : mu (forceOpenFinset F ⁻¹' B) = 0 := by
    rw [← hpush]
    exact hfe F hnull
  have hAle : mu A <= mu (forceOpenFinset F ⁻¹' B) := measure_mono hsub
  rw [hpre0] at hAle
  exact (not_lt_of_ge hAle) hApos


theorem PeriodicGraph.numInfiniteClusters_zero_one_or_top
    (P : PeriodicGraph V) (hconn : P.graph.Connected)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (herg : P.IsErgodic mu) (hfe : HasFiniteEnergy mu) :
    ∃ k : ℕ∞, mu {omega | P.numInfiniteClusters omega = k} = 1 ∧
      (k = 0 ∨ k = 1 ∨ k = ⊤) := by
  obtain ⟨k, hk⟩ := P.numInfiniteClusters_ae_const mu herg
  refine ⟨k, hk, ?_⟩
  by_cases htop : k = ⊤
  · exact Or.inr (Or.inr htop)
  have hnot2 : ¬ 2 <= k := by
    intro hk2
    exact P.numInfiniteClusters_const_ne_finite_two hconn mu hfe hk hk2 htop
  have hle : k <= 1 := StatMech.Percolation.enat_le_one_of_not_two hnot2
  rcases ENat.le_one_iff_eq_zero_or_eq_one.mp hle with hzero | hone
  · exact Or.inl hzero
  · exact Or.inr (Or.inl hone)

end StatMech.FK.PeriodicPlanar
