/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTTransport.Part3


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


def triHexTorusTriangleEdgeBaseShift (L : ℕ) (i : Fin 3) : TorusSite L :=
  ![(0, 1), (1, 0), (1, 0)] i


def triHexTorusTriangleIndexEquiv (L : ℕ) :
    TriHexTorusEdgeIndex L ≃ TriHexTorusEdgeIndex L where
  toFun a := (a.1 + triHexTorusTriangleEdgeBaseShift L a.2, a.2)
  invFun a := (a.1 - triHexTorusTriangleEdgeBaseShift L a.2, a.2)
  left_inv := by
    rintro ⟨z, i⟩
    ext <;> simp
  right_inv := by
    rintro ⟨z, i⟩
    ext <;> simp


noncomputable def triHexTorusTriangleSweepEdgeEquiv (L : ℕ) [Fact (2 < L)] :
    TriHexTorusEdgeIndex L ≃ (triangularTorusGraph L).edgeSet :=
  (triHexTorusTriangleIndexEquiv L).trans
    (triangularTorusEdgeChartEquiv L)


noncomputable def triHexTorusStarSweepEdgeEquiv (L : ℕ) [Fact (2 < L)] :
    TriHexTorusEdgeIndex L ≃ (hexagonalTorusGraph L).edgeSet :=
  hexagonalTorusEdgeChartEquiv L


def triHexTorusCellTerminal (L : ℕ) (z : TorusSite L) (i : Fin 3) :
    TorusSite L :=
  z + hexagonalTorusStep L i


def triHexTriangleEdgeTerminal1 (i : Fin 3) : Fin 3 := ![1, 2, 0] i


def triHexTriangleEdgeTerminal2 (i : Fin 3) : Fin 3 := ![2, 0, 1] i


def triHexLocalDirection (config : LocalConfig) (i : Fin 3) : Bool :=
  ![config.1, config.2.1, config.2.2] i


end StatMech.FK.PeriodicPlanar
