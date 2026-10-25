/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part6
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

noncomputable def triHexPlanarFiniteStarEdgeEquiv (n : Nat) :
    (TriHexPlanarFiniteCell n × Fin 3) ≃
      (triHexPlanarFiniteStarGraph n).edgeSet :=
  Equiv.ofBijective (triHexPlanarFiniteStarEdgeChart n)
    (triHexPlanarFiniteStarEdgeChart_bijective n)


def triHexFiniteCellConfigEquiv (I : Type*) :
    ConfigSpace (I × Fin 3) ≃ (I → LocalConfig) where
  toFun omega z := (omega (z, 0), omega (z, 1), omega (z, 2))
  invFun config a := ![config a.1 |>.1, config a.1 |>.2.1,
    config a.1 |>.2.2] a.2
  left_inv omega := by
    funext a
    rcases a with ⟨z, i⟩
    fin_cases i <;> rfl
  right_inv config := by
    funext z
    rfl


noncomputable def triHexPlanarFiniteTriangleConfigEquiv (n : Nat) :
    ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet ≃
      (TriHexPlanarFiniteCell n → LocalConfig) :=
  (configReindexEquiv (triHexPlanarFiniteTriangleEdgeEquiv n)).trans
    (triHexFiniteCellConfigEquiv _)


noncomputable def triHexPlanarFiniteStarConfigEquiv (n : Nat) :
    ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet ≃
      (TriHexPlanarFiniteCell n → LocalConfig) :=
  (configReindexEquiv (triHexPlanarFiniteStarEdgeEquiv n)).trans
    (triHexFiniteCellConfigEquiv _)

end
end StatMech.FK.PeriodicPlanar
