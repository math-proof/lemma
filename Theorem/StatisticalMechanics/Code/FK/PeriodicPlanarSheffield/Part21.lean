/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part21
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicGraph.pairMergeErrorUnion_real_tendsto_zero
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (L R : Finset V) :
    Tendsto (fun N => mu.real (P.pairMergeErrorUnion L R N))
      atTop (nhds 0) := by
  let F : ℕ → ℝ := fun N =>
    ∑ x ∈ L, ∑ y ∈ R, mu.real (P.pairMergeError x y N)
  have hF : Tendsto F atTop (nhds 0) := by
    dsimp [F]
    convert tendsto_finsetSum L (fun x _ =>
      tendsto_finsetSum R (fun y _ =>
        P.pairMergeError_real_tendsto_zero mu hunique x y)) using 1 <;> simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF
  · intro N
    exact measureReal_nonneg
  · intro N
    exact le_trans (measureReal_biUnion_finset_le _ _)
      (Finset.sum_le_sum fun x _ => measureReal_biUnion_finset_le _ _)

theorem PeriodicGraph.hasUniqueInfiniteCluster_translate_preimage
    (P : PeriodicGraph V) (z : Site 2) :
    P.configTranslate z ⁻¹'
        {omega | P.HasUniqueInfiniteCluster omega} =
      {omega | P.HasUniqueInfiniteCluster omega} := by
  ext omega
  exact P.hasUniqueInfiniteCluster_configTranslate z omega

theorem PeriodicGraph.clusterInfinite_translate_preimage
    (P : PeriodicGraph V) (z : Site 2) (x : V) :
    P.configTranslate z ⁻¹'
        {omega | (P.cluster omega (P.shift z x)).Infinite} =
      {omega | (P.cluster omega x).Infinite} := by
  ext omega
  exact P.cluster_infinite_configTranslate z omega x


theorem PeriodicGraph.exists_fundamental_clusterInfinite_pos
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] (hTI : P.IsTranslationInvariant mu)
    (hexists : mu {omega | P.HasInfiniteCluster omega} = 1) :
    ∃ u ∈ P.fundamentalDomain,
      0 < mu {omega | (P.cluster omega u).Infinite} := by
  by_contra hnone
  push Not at hnone
  have hrepzero : ∀ u ∈ P.fundamentalDomain,
      mu {omega | (P.cluster omega u).Infinite} = 0 := by
    intro u hu
    exact le_antisymm (hnone u hu) bot_le
  have hallzero : ∀ x : V,
      mu {omega | (P.cluster omega x).Infinite} = 0 := by
    intro x
    obtain ⟨z, u, hu, rfl⟩ := P.covers x
    calc
      mu {omega | (P.cluster omega (P.shift z u)).Infinite} =
          mu (P.configTranslate z ⁻¹'
            {omega | (P.cluster omega (P.shift z u)).Infinite}) :=
        ((hTI z).measure_preimage
          (P.measurableSet_cluster_infinite
            (P.shift z u)).nullMeasurableSet).symm
      _ = mu {omega | (P.cluster omega u).Infinite} := by
        rw [P.clusterInfinite_translate_preimage]
      _ = 0 := hrepzero u hu
  have hunion : mu (⋃ x : V,
      {omega : ConfigSpace (Sym2 V) |
        (P.cluster omega x).Infinite}) = 0 :=
    MeasureTheory.measure_iUnion_null hallzero
  have heq : {omega : ConfigSpace (Sym2 V) |
      P.HasInfiniteCluster omega} =
      ⋃ x : V, {omega : ConfigSpace (Sym2 V) |
        (P.cluster omega x).Infinite} := by
    ext omega
    simp [PeriodicGraph.HasInfiniteCluster]
  rw [heq, hunion] at hexists
  exact one_ne_zero hexists.symm

namespace PeriodicPlanarDualPair


theorem dual_planeRect_eq
    (D : PeriodicPlanarDualPair P Pdual) (a b c d : ℝ) :
    D.dualEmbedding.planeRect a b c d =
      D.primalEmbedding.planeRect a b c d := by
  ext z
  simp only [PeriodicPlaneEmbedding.planeRect, Set.mem_setOf_eq]
  rw [D.coordinates_eq]


theorem exists_common_edgeArc_displacement_bound
    (D : PeriodicPlanarDualPair P Pdual) :
    ∃ B : ℝ, 0 < B ∧
      (∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
        |D.primalEmbedding.coordinates
          (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B) ∧
      (∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
        |D.dualEmbedding.coordinates
          (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B) := by
  obtain ⟨Bp, hBp0, hBp⟩ :=
    D.primalEmbedding.exists_edgeArc_displacement_bound
  obtain ⟨Bd, hBd0, hBd⟩ :=
    D.dualEmbedding.exists_edgeArc_displacement_bound
  let B := max Bp Bd + 1
  refine ⟨B, by dsimp [B]; linarith [le_max_left Bp Bd, hBp0], ?_, ?_⟩
  · intro x y hxy t i
    exact (hBp hxy t i).trans (by dsimp [B]; linarith [le_max_left Bp Bd])
  · intro x y hxy t i
    exact (hBd hxy t i).trans (by dsimp [B]; linarith [le_max_right Bp Bd])

theorem dualConfigEquiv_configTranslate
    (D : PeriodicPlanarDualPair P Pdual) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    dualConfigEquiv D.edgeDual (P.configTranslate z omega) =
      Pdual.configTranslate z (dualConfigEquiv D.edgeDual omega) := by
  funext e
  have hshift := D.edgeDual_shift (-z) (D.edgeDual.symm e)
  simp only [Equiv.apply_symm_apply] at hshift
  have hsymm : D.edgeDual.symm
        (Sym2.map (Pdual.shift (-z)) e) =
      Sym2.map (P.shift (-z)) (D.edgeDual.symm e) := by
    rw [← hshift]
    simp
  simp only [dualConfigEquiv_apply, PeriodicGraph.configTranslate]
  rw [hsymm]


end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
