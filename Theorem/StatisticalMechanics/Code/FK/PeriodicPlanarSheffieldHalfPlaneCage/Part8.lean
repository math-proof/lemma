/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrossingFromArms
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrosscut
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRotated
import Mathlib.Topology.Subpath
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part7
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : Real) :
    MeasurableSet (E.rightHalfPlaneBoundaryHasInfiniteCluster r) := by
  have heq : E.rightHalfPlaneBoundaryHasInfiniteCluster r =
      ⋃ b : V, ⋃ (_hb : b ∈ E.rightHalfPlaneBoundaryVertices r),
        {omega : ConfigSpace (Sym2 V) |
          (P.clusterWithinSet omega
            (E.rightHalfPlaneVertices r) b).Infinite} := by
    ext omega
    simp [PeriodicPlaneEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster]
  rw [heq]
  exact MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _hb =>
    P.measurableSet_clusterWithinSet_infinite
      (E.rightHalfPlaneVertices r) b


theorem PeriodicGraph.clusterWithinSet_infinite_of_connectedWithinSet
    (P : PeriodicGraph V) {omega : ConfigSpace (Sym2 V)}
    {A : Set V} {x b : V}
    (hinfinite : (P.clusterWithinSet omega A x).Infinite)
    (hxb : omega ∈ P.connectedWithinSet A x b) :
    (P.clusterWithinSet omega A b).Infinite := by
  obtain ⟨qxb, hqxb⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxb
  apply hinfinite.mono
  intro y hy
  obtain ⟨qxy, hqxy⟩ :=
    P.connectedWithinSet_exists_openSubgraphWalk (by simpa using hy)
  have hwalk : ∀ v ∈ (qxb.reverse.append qxy).support, v ∈ A := by
    intro v hv
    simp only [SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hv | hv
    · exact hqxb v (by simpa using hv)
    · exact hqxy v hv
  exact P.mem_connectedWithinSet_of_walk (qxb.reverse.append qxy) hwalk


theorem PeriodicPlaneEmbedding.unique_halfPlane_outside_subset_boundaryInfinite
    (E : PeriodicPlaneEmbedding P) (r : Real) (T : Set V)
    (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
    {omega : ConfigSpace (Sym2 V) | P.HasUniqueInfiniteCluster omega} ∩
      (E.rightHalfPlaneHasInfiniteCluster r ∩ P.setHitsInfinite T) ⊆
        E.rightHalfPlaneBoundaryHasInfiniteCluster r := by
  rintro omega ⟨hunique, ⟨⟨x, hxH, hxRestricted⟩,
    y, hyT, hyInfinite⟩⟩
  have hxGlobal : (P.cluster omega x).Infinite := by
    apply hxRestricted.mono
    intro z hz
    obtain ⟨q, _hq⟩ :=
      P.connectedWithinSet_exists_openSubgraphWalk (by simpa using hz)
    exact ⟨q⟩
  have hxy : (P.openSubgraph omega).Reachable x y :=
    hunique.2 x y hxGlobal hyInfinite
  obtain ⟨b, hb, hxb⟩ :=
    E.connectedWithin_rightHalfPlane_boundary_of_reachable
      omega r hxH (hT hyT) hxy
  exact ⟨b, hb,
    P.clusterWithinSet_infinite_of_connectedWithinSet hxRestricted hxb⟩


theorem PeriodicPlaneEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster_measure_eq_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) (hhalf : mu (E.rightHalfPlaneHasInfiniteCluster r) = 1) :
    mu (E.rightHalfPlaneBoundaryHasInfiniteCluster r) = 1 := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  choose z hz using fun N : Nat =>
    E.exists_shift_orbitBox_subset_leftComplement N r
  let T : Nat → Set V := fun N => P.shift (z N) '' (P.orbitBox N : Set V)
  have hToutside (N : Nat) : T N ⊆
      (E.rightHalfPlaneVertices r)ᶜ := by
    rintro _ ⟨v, hv, rfl⟩
    exact hz N v hv
  have hTmass (N : Nat) :
      mu.real (P.setHitsInfinite (T N)) =
        mu.real (P.orbitBoxHitsInfinite N) := by
    dsimp only [T]
    rw [P.setHitsInfinite_translate_measureReal_eq mu hTI (z N)]
    rfl
  have hUae : ∀ᵐ omega ∂mu,
      omega ∈ {omega | P.HasUniqueInfiniteCluster omega} :=
    (mem_ae_iff_prob_eq_one P.measurableSet_hasUniqueInfiniteCluster).2 hunique
  have hHae : ∀ᵐ omega ∂mu,
      omega ∈ E.rightHalfPlaneHasInfiniteCluster r :=
    (mem_ae_iff_prob_eq_one
      (E.rightHalfPlaneHasInfiniteCluster_measurableSet r)).2 hhalf
  have hle (N : Nat) : mu.real (P.setHitsInfinite (T N)) ≤
      mu.real (E.rightHalfPlaneBoundaryHasInfiniteCluster r) := by
    have hae : (P.setHitsInfinite (T N) : Set (ConfigSpace (Sym2 V))) ≤ᵐ[mu]
        E.rightHalfPlaneBoundaryHasInfiniteCluster r := by
      filter_upwards [hUae, hHae] with omega hU hH hT
      exact E.unique_halfPlane_outside_subset_boundaryInfinite r (T N)
        (hToutside N) ⟨hU, hH, hT⟩
    exact ENNReal.toReal_mono (measure_ne_top mu _) (measure_mono_ae hae)
  have ht := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hbound : (1 : Real) ≤
      mu.real (E.rightHalfPlaneBoundaryHasInfiniteCluster r) := by
    apply le_of_tendsto ht
    filter_upwards with N
    rw [← hTmass N]
    exact hle N
  have hreal : mu.real (E.rightHalfPlaneBoundaryHasInfiniteCluster r) = 1 :=
    le_antisymm measureReal_le_one hbound
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top mu _)
    (by norm_num : (1 : ENNReal) ≠ ⊤)).mp
  simpa [Measure.real] using hreal


end StatMech.FK.PeriodicPlanar
