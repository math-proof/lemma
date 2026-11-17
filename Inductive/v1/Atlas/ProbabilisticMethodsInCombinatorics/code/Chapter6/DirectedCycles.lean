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
open Real Finset


namespace DirectedCycles

variable {V : Type*}

/-- A directed walk in a digraph $G$ from vertex $u$ to vertex $v$: either the empty walk at
$u$, or a step along a directed edge followed by another walk. -/
public inductive DirectedWalk (G : Digraph V) : V → V → Type _
  | nil {u : V} : DirectedWalk G u u
  | cons {u v w : V} (h : G.Adj u v) (p : DirectedWalk G v w) : DirectedWalk G u w

end DirectedCycles
