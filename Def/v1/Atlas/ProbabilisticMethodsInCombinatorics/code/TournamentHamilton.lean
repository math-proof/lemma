/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamilton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.TournamentHamilton


namespace TournamentHamilton

variable {n : ℕ}

/-- A permutation $\sigma$ of $\mathrm{Fin}\, n$ encodes a Hamilton path of $T$ if each
consecutive directed edge $\sigma(i) \to \sigma(i+1)$ lies in $T$. -/
def Tournament.IsHamiltonPath (T : Tournament (Fin n)) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, (h : i.val + 1 < n) → T.edge (σ i) (σ ⟨i.val + 1, h⟩) = true

/-- A permutation $\sigma$ encodes a Hamilton cycle of $T$ if every cyclic directed edge
$\sigma(i) \to \sigma((i+1) \bmod n)$ lies in $T$. -/
def Tournament.IsHamiltonCycle (T : Tournament (Fin n)) (σ : Equiv.Perm (Fin n)) : Prop :=
  (hn : n ≥ 1) → ∀ i : Fin n, T.edge (σ i) (σ ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩) = true

end TournamentHamilton
