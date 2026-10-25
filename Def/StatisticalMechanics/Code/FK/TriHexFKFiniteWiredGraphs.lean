/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

def triHexPlanarTriangleEdgeBaseShift (i : Fin 3) : Site 2 :=
  ![![0, 1], ![1, 0], ![1, 0]] i


def triHexPlanarTriangleIndexEquiv :
    (Site 2 × Fin 3) ≃ (Site 2 × Fin 3) where
  toFun a := (a.1 + triHexPlanarTriangleEdgeBaseShift a.2, a.2)
  invFun a := (a.1 - triHexPlanarTriangleEdgeBaseShift a.2, a.2)
  left_inv := by
    rintro ⟨z, i⟩
    ext <;> simp
  right_inv := by
    rintro ⟨z, i⟩
    ext <;> simp


def triHexPlanarFiniteTriangleEdge (n : Nat)
    (a : TriHexPlanarFiniteCell n × Fin 3) :
    Sym2 (TriHexPlanarFiniteTerminal n) :=
  s(triHexPlanarFiniteTerminalMap n a.1 (triHexTriangleEdgeTerminal1 a.2),
    triHexPlanarFiniteTerminalMap n a.1 (triHexTriangleEdgeTerminal2 a.2))


end
end StatMech.FK.PeriodicPlanar
