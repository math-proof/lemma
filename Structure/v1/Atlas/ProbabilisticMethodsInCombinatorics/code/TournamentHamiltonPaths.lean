/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamiltonPaths.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Permanent
public import Theorem.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter10.Permanent
public section

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
