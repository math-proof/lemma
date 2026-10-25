/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/DirectedCycles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.DirectedCycles
open Real Finset


namespace DirectedCycles

variable {V : Type*}

namespace DirectedWalk

variable {G : Digraph V}

/-- A directed walk from a vertex to itself is a *cycle* if it has positive length and visits
each vertex at most once (no repeated vertices apart from the start/end). -/
structure IsCycle {u : V} (p : DirectedWalk G u u) : Prop where
  pos_length : p.length > 0
  support_nodup : p.support.tail.Nodup

end DirectedWalk
end DirectedCycles
