/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc3_barrierblocks
import Theorem.StatisticalMechanics.Code.Walls.bc3_rhoedgecases
import Theorem.StatisticalMechanics.Code.Walls.bc3_anchordecomp.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc3_core.Part2
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc3_CorridorClustersDisjoint (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) : Prop :=
  bc3_CrossDisjoint ω j₁ j₂ (L₁ + 1) (L₂ + 1) ∧ bc3_CrossDisjoint ω j₁ j₃ (L₁ + 1) (L₃ + 1) ∧
  bc3_CrossDisjoint ω j₂ j₁ (L₂ + 1) (L₁ + 1) ∧ bc3_CrossDisjoint ω j₂ j₃ (L₂ + 1) (L₃ + 1) ∧
  bc3_CrossDisjoint ω j₃ j₁ (L₃ + 1) (L₁ + 1) ∧ bc3_CrossDisjoint ω j₃ j₂ (L₃ + 1) (L₂ + 1)


end Walls
end StatMech
