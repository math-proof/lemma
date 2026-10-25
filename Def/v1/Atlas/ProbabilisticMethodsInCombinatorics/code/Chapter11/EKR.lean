/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter11/EKR.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter11.Containers
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option maxHeartbeats 400000

open SimpleGraph Finset Filter Real Asymptotics


namespace ErdosKleitmanRothschild

/-- The number of triangle-free (labelled) simple graphs on the vertex set $\{1, \dots, n\}$. -/
noncomputable def triangleFreeCount (n : ℕ) : ℕ :=
  Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree 3}

/-- The bipartite graph on $\{0, \dots, n-1\}$ with bipartition
$\{0, \dots, \lfloor n/2 \rfloor - 1\} \sqcup \{\lfloor n/2 \rfloor, \dots, n-1\}$ whose
edges are determined by the chosen subset $S$ of the bipartite edge set. Used as the lower
bound construction matching $2^{n^2/4}$ triangle-free graphs. -/
def bipartiteGraphOf (n : ℕ) (S : Finset (Fin (n / 2) × Fin (n - n / 2))) :
    SimpleGraph (Fin n) where
  Adj i j :=
    (∃ (a : Fin (n / 2)) (b : Fin (n - n / 2)),
      (a, b) ∈ S ∧ (i.val = a.val) ∧ (j.val = n / 2 + b.val)) ∨
    (∃ (a : Fin (n / 2)) (b : Fin (n - n / 2)),
      (a, b) ∈ S ∧ (j.val = a.val) ∧ (i.val = n / 2 + b.val))
  symm i j h := h.elim Or.inr Or.inl
  loopless := ⟨fun i h => by
    rcases h with ⟨a, b, _, ha, hb⟩ | ⟨a, b, _, ha, hb⟩ <;> omega⟩

end ErdosKleitmanRothschild
