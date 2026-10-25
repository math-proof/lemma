/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part16
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


def kwg_GeometricCutEvenMatching (P : PlanarZ2Subgraph) (t mult : ℝ) : Prop := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  exact kwg_CutEvenMatching (kwg_primalEnds P) (kwg_dualEnds P) t mult


def kwg_GeometricCutCycleDuality (P : PlanarZ2Subgraph) : Prop := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  exact ∀ F : Finset (kwg_Edge P),
    kwg_IsEven (kwg_dualEnds P) F ↔
      ∃ c : ConfigSpace P.V, kwg_cutSet (kwg_primalEnds P) c = F


end Ising
end StatMech
