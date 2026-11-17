/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/DirectedCycles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.DirectedCycles
public section

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
