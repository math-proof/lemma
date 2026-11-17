/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/HamiltonTournaments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Abbrev.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter2.HamiltonTournaments

@[expose] public section

set_option maxHeartbeats 800000

open Finset Fintype


namespace SzeleTournament

/-- The directed edge from $i$ to $j$ in tournament $T$: true if $T$ orients the edge
in the direction $i \to j$, false otherwise (including the diagonal). -/
def tournamentEdge {n : ℕ} (T : Tournament n) (i j : Fin n) : Bool :=
  if h : i < j then T ⟨(i, j), h⟩
  else if h2 : j < i then !T ⟨(j, i), h2⟩
  else false

/-- A permutation $\sigma$ of $\mathrm{Fin}\,n$ is a Hamilton path in tournament $T$
if every consecutive pair $(\sigma(i), \sigma(i+1))$ is a directed edge of $T$. -/
def IsHamiltonPath {n : ℕ} (T : Tournament n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, (h : i.val + 1 < n) →
    tournamentEdge T (σ i) (σ ⟨i.val + 1, h⟩) = true

end SzeleTournament
