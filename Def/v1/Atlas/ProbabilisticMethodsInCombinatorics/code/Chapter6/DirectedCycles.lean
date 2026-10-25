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
import Inductive.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.DirectedCycles
open Real Finset


namespace DirectedCycles

variable {V : Type*}

namespace DirectedWalk

variable {G : Digraph V}

/-- The length (number of edges) of a directed walk. -/
def length : {u v : V} → DirectedWalk G u v → ℕ
  | _, _, nil => 0
  | _, _, cons _ p => p.length + 1

/-- The list of vertices visited by a directed walk, in order. -/
def support : {u v : V} → DirectedWalk G u v → List V
  | u, _, nil => [u]
  | u, _, cons _ p => u :: p.support

/-- Concatenation of two directed walks meeting at a common vertex. -/
def append : {u v w : V} → DirectedWalk G u v → DirectedWalk G v w → DirectedWalk G u w
  | _, _, _, nil, q => q
  | _, _, _, cons h p, q => cons h (p.append q)

/-- Recast a directed walk along propositional equalities of its endpoints. -/
def cast {u v u' v' : V} (hu : u = u') (hv : v = v') :
    DirectedWalk G u v → DirectedWalk G u' v' :=
  fun p => hu ▸ hv ▸ p

end DirectedWalk
end DirectedCycles
