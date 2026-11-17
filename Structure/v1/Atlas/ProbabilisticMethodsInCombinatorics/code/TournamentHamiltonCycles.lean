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
open Finset Real


public noncomputable section

namespace TournamentHamiltonCycles

/-- A tournament on $n$ vertices: an irreflexive Boolean edge relation such that exactly one
of $\mathrm{edge}(i, j)$ or $\mathrm{edge}(j, i)$ is true for $i \ne j$. -/
structure Tournament (n : ℕ) where
  edge : Fin n → Fin n → Bool
  irrefl : ∀ i, edge i i = false
  tournament : ∀ i j, i ≠ j → (edge i j = true ↔ edge j i = false)

end TournamentHamiltonCycles
end
