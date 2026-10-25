/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CorridorSidesFromClusters.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcedpathconn
import Theorem.StatisticalMechanics.Code.Walls.bc2_cutunbounded
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcemono
import Theorem.StatisticalMechanics.Code.Walls.bc2_raydisjoint.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_threewitnesses
import Theorem.StatisticalMechanics.Code.Walls.bc2_core
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc2_PairwiseSeparated (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) : Prop :=
  ¬ Connected d (removeSite 0 (forceOpenFinset
        (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
          hrHD_corridorEdges j₃ (L₃ + 1)) ω)) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) ∧
    ¬ Connected d (removeSite 0 (forceOpenFinset
        (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
          hrHD_corridorEdges j₃ (L₃ + 1)) ω)) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1) ∧
    ¬ Connected d (removeSite 0 (forceOpenFinset
        (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
          hrHD_corridorEdges j₃ (L₃ + 1)) ω)) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)


def bc2_ForcedCorridorRouting (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ),
    (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
    ((cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite ∧
      (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite ∧
      (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite) ∧
    bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃


end Walls
end StatMech
