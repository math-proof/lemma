/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/Sampling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
set_option maxHeartbeats 400000

open Finset Nat


namespace Sampling

variable {n : ℕ}

/-- A hypergraph $E$ on $\mathrm{Fin}\,n$ is 3-uniform if every hyperedge has exactly
$3$ elements. -/
def IsThreeUniform (E : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ E, e.card = 3

/-- A 3-uniform hypergraph $E$ is tetrahedron-free if no $4$-vertex subset
contains $4$ hyperedges (i.e., all four triples in some $4$-set), equivalently every
$4$-set spans at most $3$ hyperedges. -/
def IsTetrahedronFree (E : Finset (Finset (Fin n))) : Prop :=
  ∀ S ∈ powersetCard 4 (univ : Finset (Fin n)),
    ((S.powersetCard 3).filter (· ∈ E)).card ≤ 3

/-- A $3$-uniform hypergraph on $\mathrm{Fin}\,5$ contains a tetrahedron if some
$4$-vertex subset $T$ has all four of its $3$-element subsets as hyperedges. -/
def ContainsTetrahedron (H : Finset (Finset (Fin 5))) : Prop :=
  ∃ T ∈ powersetCard 4 (univ : Finset (Fin 5)), powersetCard 3 T ⊆ H

/-- A $3$-uniform hypergraph on $\mathrm{Fin}\,5$ is tetrahedron-free if it does not
contain a tetrahedron. -/
def IsTetrahedronFree5 (H : Finset (Finset (Fin 5))) : Prop :=
  ¬ContainsTetrahedron H

end Sampling
