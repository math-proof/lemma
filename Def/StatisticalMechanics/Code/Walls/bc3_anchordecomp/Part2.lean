/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_anchordecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc3_anchordecomp
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


noncomputable def bc3_corridorUnion (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    Finset (Sym2 (Site d)) :=
  hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
    hrHD_corridorEdges j₃ (L₃ + 1)


end Walls
end StatMech
