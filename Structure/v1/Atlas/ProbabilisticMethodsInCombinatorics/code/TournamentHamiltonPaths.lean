/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamiltonPaths.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.Permanent
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Permanent
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter10.Permanent
set_option maxHeartbeats 3200000

open Real Finset BigOperators


namespace TournamentHamiltonPaths

/-- A tournament on $n$ vertices: an irreflexive, complete, asymmetric directed-edge
relation on $\mathrm{Fin}\, n$, equipped with a decidability instance. -/
structure Tournament (n : ℕ) where
  edge : Fin n → Fin n → Prop
  irrefl : ∀ i, ¬ edge i i
  complete : ∀ i j, i ≠ j → (edge i j ∨ edge j i)
  antisymm : ∀ i j, edge i j → ¬ edge j i
  [decEdge : DecidableRel edge]

end TournamentHamiltonPaths
