/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalPlusCorrDecay
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderLimit.Part3
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

theorem map_product_embeddings
    {A B C D : Type*} [DecidableEq A] [DecidableEq B]
    [DecidableEq C] [DecidableEq D]
    (e : A ↪ B) (f : C ↪ D) (s : Finset A) (t : Finset C) :
    (s.product t).map (e.prodMap f) = (s.map e).product (t.map f) := by
  ext uv
  constructor
  · intro huv
    obtain ⟨xy, hxy, hEq⟩ := Finset.mem_map.mp huv
    have hmem := Finset.mem_product.mp hxy
    subst uv
    exact Finset.mem_product.mpr
      ⟨Finset.mem_map.mpr ⟨xy.1, hmem.1, rfl⟩,
       Finset.mem_map.mpr ⟨xy.2, hmem.2, rfl⟩⟩
  · intro huv
    have hmem := Finset.mem_product.mp huv
    obtain ⟨x, hxs, hx⟩ := Finset.mem_map.mp hmem.1
    obtain ⟨y, hyt, hy⟩ := Finset.mem_map.mp hmem.2
    exact Finset.mem_map.mpr
      ⟨(x, y), Finset.mem_product.mpr ⟨hxs, hyt⟩,
       Prod.ext hx hy⟩

theorem centralCylinderPairs_map_internal
    (n m : Nat) (hnm : centralSquareSide n < m) :
    (centralCylinderPairs n).map
        ((internalCentralVertexEmbedding n m hnm).prodMap
          (internalCentralVertexEmbedding n m hnm)) =
      (cubicalInternalCentralBoundaryVertices (centralSquareSide n) m).product
        (cubicalInternalCentralUpperVertices
          (centralSquareSide n) m hnm.le) := by
  unfold centralCylinderPairs
  rw [map_product_embeddings,
    centralLowerBoundaryVertices_map_internal,
    cubicalInternalCentralUpperVertices_eq_coordinate
      (centralSquareSide n) m (by simp [centralSquareSide]) hnm.le,
    centralUpperLayerVertices_map_internal]


theorem cubicalInternalCentralWilsonExpectation_ge_fixed_product
    (n m : Nat) (hnm : centralSquareSide n < m)
    (K : Real) (hK : 0 < K) :
    (∏ uv ∈ centralCylinderPairs n,
      (1 - multibondIsingTwoPoint cubicalDualEnds
        (fun _ : CubicalPlaquette (oddCubeSide m) (oddCubeSide m)
          (oddCubeSide m) => gaugeDualCoupling K)
        (internalCentralVertexEmbedding n m hnm uv.1)
        (internalCentralVertexEmbedding n m hnm uv.2))) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence (fun _ => K)
        (gaugeSurfaceBoundary cubicalPlaquetteIncidence
          (cubicalInternalCentralSheet
            (centralSquareSide n) m hnm.le)) := by
  let e := internalCentralVertexEmbedding n m hnm
  let pairE := e.prodMap e
  let corr := fun uv :
      CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) ×
        CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) =>
    multibondIsingTwoPoint cubicalDualEnds
      (fun _ : CubicalPlaquette (oddCubeSide m) (oddCubeSide m)
        (oddCubeSide m) => gaugeDualCoupling K) uv.1 uv.2
  let actual :=
    (cubicalInternalCentralInnerVertices
      (centralSquareSide n) m hnm.le).product
    (cubicalInternalCentralUpperVertices
      (centralSquareSide n) m hnm.le)
  let boundary :=
    (cubicalInternalCentralBoundaryVertices
      (centralSquareSide n) m).product
    (cubicalInternalCentralUpperVertices
      (centralSquareSide n) m hnm.le)
  have hsub : actual ⊆ boundary := by
    intro uv huv
    have hmem := Finset.mem_product.mp huv
    exact Finset.mem_product.mpr
      ⟨cubicalInternalCentralInnerVertices_subset_boundary
        (centralSquareSide n) m (by simp [centralSquareSide]) hnm hmem.1,
       hmem.2⟩
  have hJ0 : forall p : CubicalPlaquette (oddCubeSide m) (oddCubeSide m)
      (oddCubeSide m), 0 <= gaugeDualCoupling K := fun _ =>
    (gaugeDualCoupling_pos hK).le
  have hfactor0 : ∀ uv, uv ∈ boundary -> 0 <= 1 - corr uv := by
    intro uv _
    exact sub_nonneg.mpr
      (multibondIsingTwoPoint_le_one_of_nonneg cubicalDualEnds _ hJ0 _ _)
  have hfactor1 : ∀ uv, uv ∈ boundary -> uv ∉ actual ->
      1 - corr uv <= 1 := by
    intro uv _ _
    linarith [multibondIsingTwoPoint_nonneg_of_nonneg
      cubicalDualEnds _ hJ0 uv.1 uv.2]
  calc
    (∏ uv ∈ centralCylinderPairs n,
        (1 - multibondIsingTwoPoint cubicalDualEnds
          (fun _ : CubicalPlaquette (oddCubeSide m) (oddCubeSide m)
            (oddCubeSide m) => gaugeDualCoupling K)
          (e uv.1) (e uv.2))) =
        ∏ uv ∈ boundary, (1 - corr uv) := by
      change (∏ uv ∈ centralCylinderPairs n,
        (1 - corr (pairE uv))) = _
      calc
        _ = ∏ uv ∈ (centralCylinderPairs n).map pairE,
            (1 - corr uv) :=
          (Finset.prod_map (centralCylinderPairs n) pairE
            (fun uv => 1 - corr uv)).symm
        _ = _ := by rw [centralCylinderPairs_map_internal]
    _ <= ∏ uv ∈ actual, (1 - corr uv) :=
      Finset.prod_le_prod_of_subset_of_le_one hsub hfactor0 hfactor1
    _ <= gaugeWilsonExpectation cubicalPlaquetteIncidence (fun _ => K)
        (gaugeSurfaceBoundary cubicalPlaquetteIncidence
          (cubicalInternalCentralSheet
            (centralSquareSide n) m hnm.le)) := by
      exact cubicalInternalCentralWilsonExpectation_ge_product
        (centralSquareSide n) m (by simp [centralSquareSide]) hnm.le
        (fun _ => K) (fun _ => hK)


end
end StatMech.FrontierA
