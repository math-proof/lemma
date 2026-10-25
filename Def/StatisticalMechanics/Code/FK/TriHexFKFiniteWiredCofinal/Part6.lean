/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part6
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

def triHexPlanarHexBufferedOuterStarLevel (n : Nat) : Nat :=
  hexagonal.bufferedRadius (n + 1) + 1


noncomputable def triHexPlanarHexBufferedToFiniteStar (n : Nat) :
    hexagonal.BufferedVertex n ↪
      TriHexPlanarFiniteStarVertex
        (triHexPlanarHexBufferedOuterStarLevel n) where
  toFun v := Classical.choose
    (hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ
      (hexagonal.bufferedRadius (n + 1))
      (hexagonal.orbitBox_mono
        (hexagonal.bufferedRadius_strictMono.monotone (Nat.le_succ n)) v.2))
  inj' x y h := by
    apply Subtype.ext
    have hx := Classical.choose_spec
      (hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ
        (hexagonal.bufferedRadius (n + 1))
        (hexagonal.orbitBox_mono
          (hexagonal.bufferedRadius_strictMono.monotone (Nat.le_succ n)) x.2))
    have hy := Classical.choose_spec
      (hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ
        (hexagonal.bufferedRadius (n + 1))
        (hexagonal.orbitBox_mono
          (hexagonal.bufferedRadius_strictMono.monotone (Nat.le_succ n)) y.2))
    exact hx.symm.trans ((congrArg
      (triHexPlanarFiniteStarVertexEmbedding
        (hexagonal.bufferedRadius (n + 1) + 1)) h).trans hy)

end
end StatMech.FK.PeriodicPlanar
