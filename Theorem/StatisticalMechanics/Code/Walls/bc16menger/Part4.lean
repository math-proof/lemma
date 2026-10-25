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
import Def.StatisticalMechanics.Code.Walls.bc16menger.Part3


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}


theorem bc16_one_le_ncard_separator_of_path {S T C : Set V} {s t : V}
    (hs : s ∈ S) (ht : t ∈ T) {p : G.Walk s t} (hp : p.IsPath)
    (hC : bc16_IsSeparator G S T C) (hCfin : C.Finite) :
    1 ≤ C.ncard := by
  have h := bc16_max_le_min (bc16_singletonFamily hs ht hp) hC hCfin
  rwa [Set.ncard_univ, Nat.card_unique] at h


theorem bc16_encard_le_source_target {S T : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) :
    (Set.univ : Set ι).encard ≤ S.encard ∧ (Set.univ : Set ι).encard ≤ T.encard :=
  ⟨bc16_encard_le_encard_separator F (bc16_source_isSeparator G S T),
   bc16_encard_le_encard_separator F (bc16_target_isSeparator G S T)⟩

end StatMech.Walls
