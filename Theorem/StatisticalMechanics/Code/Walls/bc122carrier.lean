/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc121trifcount.Part2
import Def.StatisticalMechanics.Code.Walls.bc122carrier
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc122_carrier_closes (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc122_StarOfArms ω L R) : bc69_Gn_globalForest ω L R := by
  classical
  obtain ⟨S, hSfin, hSne, G, hGdec, ιU, hGac, harmAdj, hinj, hFmin⟩ := h
  refine bc121_globalForest_of_peel2 ω L R G hGac ιU ?_ hinj hFmin
  intro y hybox htri
  obtain ⟨t₁, t₂, t₃, hp₁, hp₂, hp₃, ha₁, ha₂, ha₃, hc₁₂, hc₁₃, hc₂₃⟩ := harmAdj y hybox htri
  exact ⟨t₁, t₂, t₃, hp₁, hp₂, hp₃,
    ha₁.ne, ha₂.ne, ha₃.ne,
    ha₁.reachable, ha₂.reachable, ha₃.reachable, hc₁₂, hc₁₃, hc₂₃⟩


theorem bc122_count_via_carrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc122_StarOfArms ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc118_count_closes_via_forest ω L R (bc122_carrier_closes ω L R h)


end StatMech.Walls
