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
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part21
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


noncomputable def kwg_DualContourMatching (P : PlanarZ2Subgraph)
    (β βstar c : ℝ) : Prop := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  exact Real.tanh βstar = Real.exp (-2 * β) ∧
    (2 : ℝ) ^ Nat.card (kwg_Face P) *
        (Real.cosh βstar) ^ Nat.card (kwg_Edge P) *
        (∑ F : Finset (kwg_Edge P),
          if kwg_IsEven (kwg_dualEnds P) F then (Real.tanh βstar) ^ F.card else 0)
      = c * isingZ P.G β 0


end Ising
end StatMech
