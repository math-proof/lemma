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
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


def configReindexEquiv {E I : Type*} (e : I ≃ E) :
    ConfigSpace E ≃ ConfigSpace I where
  toFun omega i := omega (e i)
  invFun config a := config (e.symm a)
  left_inv omega := by
    funext a
    simp
  right_inv config := by
    funext i
    simp


def triHexTorusCellConfigEquiv (L : ℕ) :
    ConfigSpace (TriHexTorusEdgeIndex L) ≃
      (TorusSite L → LocalConfig) where
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


noncomputable def triangularTorusActiveConfigEquiv (L : ℕ) [Fact (2 < L)] :
    ConfigSpace (triangularTorusGraph L).edgeSet ≃
      (TorusSite L → LocalConfig) :=
  (configReindexEquiv (triHexTorusTriangleSweepEdgeEquiv L)).trans
    (triHexTorusCellConfigEquiv L)


noncomputable def hexagonalTorusActiveConfigEquiv (L : ℕ) [Fact (2 < L)] :
    ConfigSpace (hexagonalTorusGraph L).edgeSet ≃
      (TorusSite L → LocalConfig) :=
  (configReindexEquiv (triHexTorusStarSweepEdgeEquiv L)).trans
    (triHexTorusCellConfigEquiv L)

end StatMech.FK.PeriodicPlanar
