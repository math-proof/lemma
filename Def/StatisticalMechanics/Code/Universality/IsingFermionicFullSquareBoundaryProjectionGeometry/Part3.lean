/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection.Part3
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def FullSquareOrdinaryBoundaryProjectionTraceData.ofSideTraces
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (L : Nat -> NNReal) (S : Nat -> Set Complex)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im) (S k))
    (hleftTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
        (fullSquareScaledLeftSide (N k) (mesh k)))
    (hfreeTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
        (fullSquareScaledFreeSides (N k) (mesh k)))
    (hvertexFixed_mem : forall k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x ->
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ S k)
    (hfaceFixed_mem : forall k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c ->
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ S k /\
        fullSquareFaceFixedBoundaryProjection (N k) (mesh k) c ∈ S k)
    (hvertexFree_mem : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        fullSquareScaledVertexEmbedding (N k) (mesh k) x ∈ S k)
    (hfaceFree_mem : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        fullSquareScaledFaceEmbedding (N k) (mesh k) c ∈ S k /\
        fullSquareFaceFreeBoundaryProjection (N k) (mesh k) c ∈ S k) :
    FullSquareOrdinaryBoundaryProjectionTraceData N Phi mesh radius where
  lipschitzConstant := L
  region := S
  imPhi_lipschitz := hPhi
  vertexFixed k x hfixed hghost :=
    ⟨hvertexFixed_mem k x hfixed hghost,
      hleftTrace k
        (fullSquareVertexBoundaryProjection_mem_leftSide
          (N k) (mesh k) x hfixed)⟩
  faceFixed k c hfixed hghost :=
    ⟨(hfaceFixed_mem k c hfixed hghost).1,
      (hfaceFixed_mem k c hfixed hghost).2,
      hfreeTrace k
        (fullSquareFaceFixedBoundaryProjection_mem_freeSides
          (N k) (mesh k) c hfixed)⟩
  vertexFree k x hfixed hghost hendpoint :=
    ⟨hvertexFree_mem k x hfixed hghost hendpoint,
      hfreeTrace k
        (fullSquareVertexFreeBoundaryProjection_mem_freeSides
          (N k) (mesh k) x hghost)⟩
  faceFree k c hfixed hghost hendpoint :=
    ⟨(hfaceFree_mem k c hfixed hghost hendpoint).1,
      (hfaceFree_mem k c hfixed hghost hendpoint).2,
      hleftTrace k
        (fullSquareFaceFreeBoundaryProjection_mem_leftSide
          (N k) (mesh k) c hghost)⟩


def fullSquareOrdinaryBoundaryProjectionCarrier
    (n : Nat) (mesh : Real) (radius : Nat) : Set Complex :=
  {z |
    (∃ x : FKIsingSquareFullVertexNode n,
      fkIsingSquareFullVertexFixedBoundary n x ∧
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity n x) ∧
        (z = fullSquareScaledVertexEmbedding n mesh x ∨
          z = fullSquareVertexBoundaryProjection n mesh x)) ∨
    (∃ c : FKIsingSquareFullFaceNode n,
      fkIsingSquareFullFaceFixedBoundary n c ∧
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity n c) ∧
        (z = fullSquareScaledFaceEmbedding n mesh c ∨
          z = fullSquareFaceFixedBoundaryProjection n mesh c)) ∨
    (∃ x : FKIsingSquareFullVertexNode n,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ∧
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ∧
      Not (vertexMarkedEndpointLayer n radius (some x)) ∧
        (z = fullSquareScaledVertexEmbedding n mesh x ∨
          z = fullSquareVertexFreeBoundaryProjection n mesh x)) ∨
    (∃ c : FKIsingSquareFullFaceNode n,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ∧
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ∧
      Not (faceMarkedEndpointLayer n radius (some c)) ∧
        (z = fullSquareScaledFaceEmbedding n mesh c ∨
          z = fullSquareFaceFreeBoundaryProjection n mesh c))}


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
