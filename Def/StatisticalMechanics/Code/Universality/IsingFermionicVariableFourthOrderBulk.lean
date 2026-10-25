/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVariableFourthOrderBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointInputAssembly
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk


namespace StatMech.Universality

open Filter

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def
    PhysicalEndpointVariableFourthOrderBulkData.ofAnalyticTensorNormOnSegments
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (U : Nat -> Set Complex) (hU : forall k, IsOpen (U k))
    (hPhi : forall k, AnalyticOnNhd Complex Phi (U k))
    (M : Nat -> NNReal)
    (htensor : forall k w, w ∈ U k ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M k)
    (hvertex : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      let z := fullSquareScaledVertexEmbedding (N k) (mesh k) x
      Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (mesh k)) (U k) /\
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (-mesh k)) (U k) /\
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (mesh k)) (U k) /\
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (-mesh k)) (U k))
    (hface : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      let z := fullSquareScaledFaceEmbedding (N k) (mesh k) c
      Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (mesh k)) (U k) /\
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 + Complex.I))
          (Set.uIcc 0 (-mesh k)) (U k) /\
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (mesh k)) (U k) /\
        Set.MapsTo
          (fun t : Real => z + (t : Complex) * (1 - Complex.I))
          (Set.uIcc 0 (-mesh k)) (U k)) :
    PhysicalEndpointVariableFourthOrderBulkData N Phi mesh radius where
  boundOne k := 4 * (M k : Real)
  boundTwo k := 4 * (M k : Real)
  boundSum_nonneg k := by positivity
  vertex k x hfixed hghost hendpoint := by
    obtain ⟨hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hvertex k x hfixed hghost hendpoint
    exact LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
      (U k) (hU k) (hPhi k) (M k) (htensor k)
      hpositiveOne hnegativeOne hpositiveTwo hnegativeTwo
  face k c hfixed hghost hendpoint := by
    obtain ⟨hpositiveOne, hnegativeOne, hpositiveTwo, hnegativeTwo⟩ :=
      hface k c hfixed hghost hendpoint
    exact LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
      (U k) (hU k) (hPhi k) (M k) (htensor k)
      hpositiveOne hnegativeOne hpositiveTwo hnegativeTwo

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
