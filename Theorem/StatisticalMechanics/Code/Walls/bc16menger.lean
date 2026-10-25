/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Def.StatisticalMechanics.Code.Walls.bc16menger


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}


theorem bc16_univ_isSeparator (G : SimpleGraph V) (S T : Set V) :
    bc16_IsSeparator G S T Set.univ := by
  intro s _ t _ p
  exact ⟨s, Set.mem_univ s, p.start_mem_support⟩


theorem bc16_separator_mono {S T C C' : Set V} (h : bc16_IsSeparator G S T C)
    (hCC' : C ⊆ C') : bc16_IsSeparator G S T C' := by
  intro s hs t ht p
  obtain ⟨c, hcC, hcp⟩ := h hs ht p
  exact ⟨c, hCC' hcC, hcp⟩


theorem bc16_separator_symm {S T C : Set V} (h : bc16_IsSeparator G S T C) :
    bc16_IsSeparator G T S C := by
  intro t ht s hs p
  obtain ⟨c, hcC, hcp⟩ := h hs ht p.reverse
  refine ⟨c, hcC, ?_⟩
  rwa [Walk.support_reverse, List.mem_reverse] at hcp


end StatMech.Walls
