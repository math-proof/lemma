/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Nodup
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Structure.v1.Atlas.TheoryOfComputation.code.Tableau
import Structure.v1.Atlas.TheoryOfComputation.code.NPCompleteness


namespace CookLevin

open TuringMachine NPCompleteness

/--
`p` is a *Hamiltonian path* from `s` to `t` in the directed graph `G` if it starts
at `s`, ends at `t`, every consecutive pair of vertices is connected by an edge of
`G`, the vertices in `p` are pairwise distinct (`Nodup`), and every vertex of `V`
appears in `p`.
-/
def DiGraph.IsHamiltonianPath (V : Type*) [DecidableEq V] [Fintype V]
    (G : DiGraph V) (s t : V) (p : List V) : Prop :=
  p.head? = some s ∧
  p.getLast? = some t ∧
  (∀ (i : ℕ) (hi : i + 1 < p.length),
    G.edge (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, hi⟩)) ∧
  p.Nodup ∧
  ∀ v : V, v ∈ p

/-- `G` has a Hamiltonian path from `s` to `t` if some list `p` is one. -/
def DiGraph.HasHamiltonianPath (V : Type*) [DecidableEq V] [Fintype V]
    (G : DiGraph V) (s t : V) : Prop :=
  ∃ p : List V, G.IsHamiltonianPath V s t p

/-- `HAMPATH = { (G, s, t) | G has a Hamiltonian path from s to t }`. -/
def HAMPATH (V : Type*) [DecidableEq V] [Fintype V] :
    Set (DiGraph V × V × V) :=
  {gst | gst.1.HasHamiltonianPath V gst.2.1 gst.2.2}

end CookLevin
