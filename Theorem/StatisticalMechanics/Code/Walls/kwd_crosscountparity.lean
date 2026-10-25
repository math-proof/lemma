/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Def.StatisticalMechanics.Code.Walls.kwd_crosscountparity
open Finset Set SimpleGraph
open StatMech.Lattice


namespace StatMech.Walls

@[simp] theorem kwd_crossCount_nil {V : Type*} {G : SimpleGraph V} (B : Sym2 V → Bool)
    (x : V) :
    kwd_crossCount B (SimpleGraph.Walk.nil : G.Walk x x) = 0 := by
  simp [kwd_crossCount]


theorem kwd_crossCount_cons {V : Type*} {G : SimpleGraph V} (B : Sym2 V → Bool)
    {a b c : V} (hab : G.Adj a b) (p : G.Walk b c) :
    kwd_crossCount B (SimpleGraph.Walk.cons hab p)
      = (if B s(a, b) then 1 else 0) + kwd_crossCount B p := by
  rw [kwd_crossCount, kwd_crossCount, SimpleGraph.Walk.edges_cons, List.countP_cons]
  by_cases h : B s(a, b)
  · rw [if_pos h]; ring
  · rw [if_neg h]; ring


theorem kwd_crossCount_append {V : Type*} {G : SimpleGraph V} (B : Sym2 V → Bool)
    {x y z : V} (p : G.Walk x y) (q : G.Walk y z) :
    kwd_crossCount B (p.append q) = kwd_crossCount B p + kwd_crossCount B q := by
  rw [kwd_crossCount, kwd_crossCount, kwd_crossCount,
    SimpleGraph.Walk.edges_append, List.countP_append]


theorem kwd_crossCount_reverse {V : Type*} {G : SimpleGraph V} (B : Sym2 V → Bool)
    {x y : V} (w : G.Walk x y) :
    kwd_crossCount B w.reverse = kwd_crossCount B w := by
  rw [kwd_crossCount, kwd_crossCount, SimpleGraph.Walk.edges_reverse, List.countP_reverse]


end StatMech.Walls
