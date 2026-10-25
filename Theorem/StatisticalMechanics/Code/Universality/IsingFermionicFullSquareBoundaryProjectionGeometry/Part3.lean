/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry.Part3


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem fullSquareOrdinaryBoundaryProjectionCarrier_finite
    (n : Nat) (mesh : Real) (radius : Nat) :
    (fullSquareOrdinaryBoundaryProjectionCarrier n mesh radius).Finite := by
  have hvertexFixed :=
    (Set.finite_range
      (fun x : FKIsingSquareFullVertexNode n =>
        fullSquareScaledVertexEmbedding n mesh x)).union
      (Set.finite_range
        (fun x : FKIsingSquareFullVertexNode n =>
          fullSquareVertexBoundaryProjection n mesh x))
  have hfaceFixed :=
    (Set.finite_range
      (fun c : FKIsingSquareFullFaceNode n =>
        fullSquareScaledFaceEmbedding n mesh c)).union
      (Set.finite_range
        (fun c : FKIsingSquareFullFaceNode n =>
          fullSquareFaceFixedBoundaryProjection n mesh c))
  have hvertexFree :=
    (Set.finite_range
      (fun x : FKIsingSquareFullVertexNode n =>
        fullSquareScaledVertexEmbedding n mesh x)).union
      (Set.finite_range
        (fun x : FKIsingSquareFullVertexNode n =>
          fullSquareVertexFreeBoundaryProjection n mesh x))
  have hfaceFree :=
    (Set.finite_range
      (fun c : FKIsingSquareFullFaceNode n =>
        fullSquareScaledFaceEmbedding n mesh c)).union
      (Set.finite_range
        (fun c : FKIsingSquareFullFaceNode n =>
          fullSquareFaceFreeBoundaryProjection n mesh c))
  refine
    (hvertexFixed.union (hfaceFixed.union
      (hvertexFree.union hfaceFree))).subset ?_
  intro z hz
  rcases hz with
      ⟨x, _hfixed, _hghost, rfl | rfl⟩ |
      ⟨c, _hfixed, _hghost, rfl | rfl⟩ |
      ⟨x, _hfixed, _hghost, _hendpoint, rfl | rfl⟩ |
      ⟨c, _hfixed, _hghost, _hendpoint, rfl | rfl⟩ <;>
    simp


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
