/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectEndpoint
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint
open MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Sharpness StatMech.FrontierB

noncomputable section

def ons_box2GraphIsoRect (n : Nat) :
    sctBoxGraph 2 n ≃g ons_rectDualGraph (2 * n) (2 * n) where
  toEquiv := ons_box2EquivRect n
  map_rel_iff' := by
    intro x y
    exact (ons_box2EquivRect_adj n x y).symm


def ons_rectDualPathOfBoxVertices (n : Nat) (x y : sctBox 2 n) (hxy : x ≠ y) :
    ons_RectDualPath (2 * n) (2 * n) where
  source := ons_box2GraphIsoRect n x
  target := ons_box2GraphIsoRect n y
  source_ne_target := fun h => hxy ((ons_box2GraphIsoRect n).injective h)
  walk := (StatMech.FrontierB.boxGraphPath 2 n x y).map
    (ons_box2GraphIsoRect n).toHom
  isPath := SimpleGraph.Walk.map_isPath_of_injective
    (f := (ons_box2GraphIsoRect n).toHom)
    (p := StatMech.FrontierB.boxGraphPath 2 n x y)
    (ons_box2GraphIsoRect n).injective
    (StatMech.FrontierB.boxGraphPath_isPath 2 n x y)


def ons_originNeighborRectDualPath (n : Nat) :
    ons_RectDualPath (2 * (n + 1)) (2 * (n + 1)) where
  source := ons_box2EquivRect (n + 1) (ons_originPositiveBoxVertex n)
  target := ons_box2EquivRect (n + 1) (ons_neighborPositiveBoxVertex n)
  source_ne_target := fun h =>
    ons_originPositiveBoxVertex_ne_neighbor n
      ((ons_box2EquivRect (n + 1)).injective h)
  walk := .cons
    ((ons_box2EquivRect_adj (n + 1) _ _).mp
      (ons_originPositiveBoxVertex_adj_neighbor n)) .nil
  isPath := by
    simp [ons_originPositiveBoxVertex_ne_neighbor]

end
end StatMech.Onsager
