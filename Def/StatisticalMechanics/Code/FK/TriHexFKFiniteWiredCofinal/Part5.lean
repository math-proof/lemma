module
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
public import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part5
open Finset Set SimpleGraph Filter MeasureTheory Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

def triHexPlanarFiniteStarToHexBuffered (n : Nat) :
    TriHexPlanarFiniteStarVertex n ↪ hexagonal.BufferedVertex (n + 2) where
  toFun v := ⟨triHexPlanarFiniteStarVertexEmbedding n v, by
    apply hexagonal.orbitBox_mono
      ((Nat.succ_le_succ (Nat.le_succ n)).trans
        (hexagonal.id_le_bufferedRadius (n + 2)))
    exact triHexPlanarFiniteStar_range_subset_orbitBox_succ n ⟨v, rfl⟩⟩
  inj' x y h := (triHexPlanarFiniteStarVertexEmbedding n).injective
    (congrArg Subtype.val h)

end
end StatMech.FK.PeriodicPlanar
