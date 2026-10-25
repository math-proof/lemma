/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointInputAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRangeBound
import Mathlib.Analysis.Calculus.MeanValue
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicEndpointInputAssembly.Part2


namespace StatMech.Universality

open Filter Set Topology

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def PhysicalEndpointLayerIncrementData.ofLipschitzOn
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (S : Set Complex) (L : NNReal)
    (hPhi : LipschitzOnWith L (fun z => (Phi z).im) S)
    (hmesh : forall k, 0 <= mesh k)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ S /\
          forall y, (fkIsingSquareFullVertexGraph (N k)).Adj x y ->
            fullSquareScaledVertexEmbedding (N k) (mesh k) y ∈ S)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ S /\
          forall d, (fkIsingSquareFullFaceGraph (N k)).Adj c d ->
            fullSquareScaledFaceEmbedding (N k) (mesh k) d ∈ S) :
    PhysicalEndpointLayerIncrementData N Phi mesh radius where
  constant := 2 * L
  vertex k x hfixed hghost hendpoint y hxy := by
    obtain ⟨hx, hy⟩ := hvertex k x hfixed hghost hendpoint
    rw [← Real.dist_eq]
    calc
      dist
          (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im
          (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <=
          L * dist
            (fullSquareScaledVertexEmbedding (N k) (mesh k) y)
            (fullSquareScaledVertexEmbedding (N k) (mesh k) x) :=
        hPhi.dist_le_mul _ (hy y hxy) _ hx
      _ <= L * (2 * |mesh k|) := by
        gcongr
        exact fullSquareScaledVertexEmbedding_dist_le_two_abs
          (N k) (mesh k) x y hxy
      _ = (2 * L : NNReal) * mesh k := by
        rw [abs_of_nonneg (hmesh k)]
        norm_num
        ring
  face k c hfixed hghost hendpoint d hcd := by
    obtain ⟨hc, hd⟩ := hface k c hfixed hghost hendpoint
    rw [← Real.dist_eq]
    calc
      dist
          (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) d)).im
          (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <=
          L * dist
            (fullSquareScaledFaceEmbedding (N k) (mesh k) d)
            (fullSquareScaledFaceEmbedding (N k) (mesh k) c) :=
        hPhi.dist_le_mul _ (hd d hcd) _ hc
      _ <= L * (2 * |mesh k|) := by
        gcongr
        exact fullSquareScaledFaceEmbedding_dist_le_two_abs
          (N k) (mesh k) c d hcd
      _ = (2 * L : NNReal) * mesh k := by
        rw [abs_of_nonneg (hmesh k)]
        norm_num
        ring


noncomputable def PhysicalEndpointLayerIncrementData.ofFDerivBoundOnConvex
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (S : Set Complex) (L : NNReal)
    (hPhi : forall z, z ∈ S ->
      DifferentiableAt Real (fun w => (Phi w).im) z)
    (hderiv : forall z, z ∈ S ->
      ‖fderiv Real (fun w => (Phi w).im) z‖₊ <= L)
    (hconvex : Convex Real S)
    (hmesh : forall k, 0 <= mesh k)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ S /\
          forall y, (fkIsingSquareFullVertexGraph (N k)).Adj x y ->
            fullSquareScaledVertexEmbedding (N k) (mesh k) y ∈ S)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ S /\
          forall d, (fkIsingSquareFullFaceGraph (N k)).Adj c d ->
            fullSquareScaledFaceEmbedding (N k) (mesh k) d ∈ S) :
    PhysicalEndpointLayerIncrementData N Phi mesh radius :=
  PhysicalEndpointLayerIncrementData.ofLipschitzOn S L
    (hconvex.lipschitzOnWith_of_nnnorm_fderiv_le hPhi hderiv)
    hmesh hvertex hface

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
