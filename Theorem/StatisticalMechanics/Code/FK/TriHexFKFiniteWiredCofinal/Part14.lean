module
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
public import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
public import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part13
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

theorem triHexPlanarFiniteTriangleToBuffered_root (n : Nat) :
    triHexPlanarFiniteTriangleToBuffered n
        (triHexPlanarFiniteTriangleRoot n) =
      triHexPlanarTriBufferedRoot (n + 1) := by
  apply Subtype.ext
  exact triHexPlanarFiniteTriangleRoot_val n

theorem triHexPlanarTriBufferedToFiniteTerminal_root (n : Nat) :
    triHexPlanarTriBufferedToFiniteTerminal (n + 1)
        (triHexPlanarTriBufferedRoot n) =
      triHexPlanarFiniteTriangleRoot
        (triHexPlanarTriBufferedOuterLevel (n + 1)) := by
  apply Subtype.ext
  exact (triHexPlanarFiniteTriangleRoot_val _).symm

end
end StatMech.FK.PeriodicPlanar
