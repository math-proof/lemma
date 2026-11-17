/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamiltonCycles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.TournamentHamiltonCycles

@[expose] public section

open Finset Real


noncomputable section

namespace TournamentHamiltonCycles

/-- A permutation $\sigma$ encodes a Hamilton cycle of $T$ iff every directed edge
$i \to \sigma(i)$ exists in $T$ and $\sigma$ is a single $n$-cycle. -/
def IsHamiltonCycle {n : ℕ} (T : Tournament n) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ i : Fin n, T.edge i (σ i) = true) ∧ σ.IsCycle ∧ σ.support = Finset.univ

/-- The number of Hamilton cycles of $T$, counted as cycle-permutations on $\mathrm{Fin}\, n$. -/
noncomputable def Tournament.numHamiltonCycles {n : ℕ} (T : Tournament n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    (∀ i : Fin n, T.edge i (σ i) = true) ∧ σ.IsCycle ∧ σ.support = Finset.univ)).card

/-- Out-degree of vertex $i$ in $T$: the number of $j$ with $T.\mathrm{edge}(i, j)$ true. -/
def Tournament.outDeg {n : ℕ} (T : Tournament n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => T.edge i j = true)).card

end TournamentHamiltonCycles
end
