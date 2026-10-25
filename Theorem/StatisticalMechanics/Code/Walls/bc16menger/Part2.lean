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
import Structure.StatisticalMechanics.Code.Walls.bc16menger


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}


theorem bc16_separator_hits_path {S T C : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) (hC : bc16_IsSeparator G S T C) (i : ι) :
    ∃ c ∈ C, c ∈ (F.p i).support :=
  hC (F.ha i) (F.hb i) (F.p i)


end StatMech.Walls
