/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalPlusCorrDecay
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderLimit.Part4
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

theorem exists_internalCentralPairCorrelation_tendsto
    (beta : Real) (n : Nat) :
    ∃ m : Nat -> Nat, ∃ hm : ∀ k, centralSquareSide n < m k,
      Tendsto m atTop atTop ∧
      ∀ uv, uv ∈ centralCylinderPairs n ->
        Tendsto
          (fun k => internalCentralPairCorrelation beta n (m k) (hm k) uv)
          atTop
          (nhds (plusCorr 3 beta
            (centralCylinderVertexSite n uv.1)
            (centralCylinderVertexSite n uv.2))) := by
  obtain ⟨phi, hphi, hconv⟩ := plusState_isInfiniteVolumeState 3 beta 0
  let shift : Nat -> Nat := fun k => k + centralSquareSide n + 1
  let m : Nat -> Nat := fun k => phi (shift k)
  have hshift : Tendsto shift atTop atTop := by
    exact (tendsto_add_atTop_iff_nat
      (centralSquareSide n + 1)).2 tendsto_id
  have hmTop : Tendsto m atTop atTop := hphi.tendsto_atTop.comp hshift
  have hm : ∀ k, centralSquareSide n < m k := by
    intro k
    dsimp [m, shift]
    have hle := hphi.le_apply (x := k + centralSquareSide n + 1)
    omega
  have hconv' : WeakConvergesTo
      (fun k => plusMeasure 3 (m k) beta 0) (plusState 3 beta 0) := by
    simpa [m, Function.comp_def] using hconv.comp hshift
  refine ⟨m, hm, hmTop, ?_⟩
  intro uv huv
  have hmem := Finset.mem_product.mp huv
  rcases uv with ⟨u, v⟩
  cases u with
  | none =>
      exact (none_not_mem_centralLowerBoundaryVertices n hmem.1).elim
  | some q =>
      cases v with
      | none =>
          exact (none_not_mem_centralUpperLayerVertices n hmem.2).elim
      | some r =>
          have hpair := plusMeasure_pair_tendsto beta m hconv'
            (centralCylinderSite n q) (centralCylinderSite n r)
          change Tendsto
            (fun k => internalCentralPairCorrelation beta n (m k) (hm k)
              (some q, some r)) atTop
            (nhds (plusCorr 3 beta
              (centralCylinderSite n q) (centralCylinderSite n r)))
          apply hpair.congr
          intro k
          rw [internalCentralPairCorrelation]
          simp only [internalCentralVertexEmbedding_some]
          rw [oddCubicalDualTwoPoint_eq_plusMeasure_pair]
          have hqsite := oddCubicalCenteredSite_internalCentralCellEmbedding
            n (m k) (hm k) q
          have hrsite := oddCubicalCenteredSite_internalCentralCellEmbedding
            n (m k) (hm k) r
          unfold oddCubicalCenteredSite at hqsite hrsite
          rw [hqsite, hrsite]


theorem exists_internalCentralCylinderProduct_tendsto
    (beta : Real) (n : Nat) :
    ∃ m : Nat -> Nat, ∃ hm : ∀ k, centralSquareSide n < m k,
      Tendsto m atTop atTop ∧
      Tendsto
        (fun k => ∏ uv ∈ centralCylinderPairs n,
          (1 - internalCentralPairCorrelation beta n (m k) (hm k) uv))
        atTop
        (nhds (∏ uv ∈ centralCylinderPairs n,
          (1 - plusCorr 3 beta
            (centralCylinderVertexSite n uv.1)
            (centralCylinderVertexSite n uv.2)))) := by
  obtain ⟨m, hm, hmTop, hcorr⟩ :=
    exists_internalCentralPairCorrelation_tendsto beta n
  refine ⟨m, hm, hmTop, ?_⟩
  exact tendsto_finset_prod_one_sub (centralCylinderPairs n)
    (fun k uv => internalCentralPairCorrelation beta n (m k) (hm k) uv)
    (fun uv => plusCorr 3 beta
      (centralCylinderVertexSite n uv.1)
      (centralCylinderVertexSite n uv.2)) hcorr


theorem cubicalInternalCentralSheet_eq_map
    (n m : Nat) (hnm : centralSquareSide n <= m) :
    cubicalInternalCentralSheet (centralSquareSide n) m hnm =
      (cubicalXYSheet
        (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
        (0 : Fin 1)).map
        (cubicalPlaquetteChart m m m
          (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
          (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
          (by dsimp [oddCubeSide]; omega)) := by
  unfold cubicalInternalCentralSheet cubicalXYSheet
  rw [Finset.map_eq_image, Finset.image_image]
  apply Finset.image_congr
  intro ij _
  change CubicalPlaquette.xy _ _ _ =
    CubicalPlaquette.xy
      (finOffsetEmbedding m _ ij.1)
      (finOffsetEmbedding m _ ij.2)
      (finOffsetEmbedding m _ (0 : Fin 1))
  rw [CubicalPlaquette.xy.injEq]
  refine ⟨?_, ?_, ?_⟩
  · apply Fin.ext
    rfl
  · apply Fin.ext
    rfl
  · apply Fin.ext
    rfl


theorem gaugeSurfaceBoundary_cubicalInternalCentralSheet_fixed
    (n m : Nat) (hnm : centralSquareSide n <= m) :
    gaugeSurfaceBoundary cubicalPlaquetteIncidence
        (cubicalInternalCentralSheet (centralSquareSide n) m hnm) =
      (cubicalXYLoop
        (a := centralSquareSide n) (b := centralSquareSide n) (c := 0)
        (0 : Fin 1)).map
        (cubicalEdgeChart m m m
          (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
          (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
          (by dsimp [oddCubeSide]; omega)) := by
  rw [cubicalInternalCentralSheet_eq_map]
  exact gaugeSurfaceBoundary_map
    cubicalPlaquetteIncidence cubicalPlaquetteIncidence
    (cubicalEdgeChart m m m
      (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
      (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
      (by dsimp [oddCubeSide]; omega))
    (cubicalPlaquetteChart m m m
      (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
      (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
      (by dsimp [oddCubeSide]; omega))
    (cubicalPlaquetteIncidence_chart m m m
      (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
      (by dsimp [oddCubeSide, centralSquareSide] at *; omega)
      (by dsimp [oddCubeSide]; omega))
    (cubicalXYSheet (0 : Fin 1))


end
end StatMech.FrontierA
