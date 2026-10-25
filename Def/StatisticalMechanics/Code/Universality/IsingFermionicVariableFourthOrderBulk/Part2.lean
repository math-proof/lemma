/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVariableFourthOrderBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointInputAssembly
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk.Part2


namespace StatMech.Universality

open Filter

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def PhysicalEndpointVariableLayerIncrementData.ofLipschitzOn
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (S : Nat -> Set Complex) (L : Nat -> NNReal)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im) (S k))
    (hmesh : forall k, 0 <= mesh k)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ S k /\
          forall y, (fkIsingSquareFullVertexGraph (N k)).Adj x y ->
            fullSquareScaledVertexEmbedding (N k) (mesh k) y ∈ S k)
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ S k /\
          forall d, (fkIsingSquareFullFaceGraph (N k)).Adj c d ->
            fullSquareScaledFaceEmbedding (N k) (mesh k) d ∈ S k) :
    PhysicalEndpointVariableLayerIncrementData N Phi mesh radius where
  constant k := 2 * L k
  vertex k x hfixed hghost hendpoint y hxy := by
    obtain ⟨hx, hy⟩ := hvertex k x hfixed hghost hendpoint
    rw [← Real.dist_eq]
    calc
      dist
          (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) y)).im
          (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <=
          L k * dist
            (fullSquareScaledVertexEmbedding (N k) (mesh k) y)
            (fullSquareScaledVertexEmbedding (N k) (mesh k) x) :=
        (hPhi k).dist_le_mul _ (hy y hxy) _ hx
      _ <= L k * (2 * |mesh k|) := by
        gcongr
        exact fullSquareScaledVertexEmbedding_dist_le_two_abs
          (N k) (mesh k) x y hxy
      _ = (2 * L k : NNReal) * mesh k := by
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
          L k * dist
            (fullSquareScaledFaceEmbedding (N k) (mesh k) d)
            (fullSquareScaledFaceEmbedding (N k) (mesh k) c) :=
        (hPhi k).dist_le_mul _ (hd d hcd) _ hc
      _ <= L k * (2 * |mesh k|) := by
        gcongr
        exact fullSquareScaledFaceEmbedding_dist_le_two_abs
          (N k) (mesh k) c d hcd
      _ = (2 * L k : NNReal) * mesh k := by
        rw [abs_of_nonneg (hmesh k)]
        norm_num
        ring

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
