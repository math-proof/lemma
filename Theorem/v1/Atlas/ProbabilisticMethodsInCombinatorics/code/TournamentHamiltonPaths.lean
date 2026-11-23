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
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.TournamentHamiltonPaths
set_option maxHeartbeats 3200000

open Real Finset BigOperators

public section

namespace TournamentHamiltonPaths

attribute [instance] Tournament.decEdge

@[simp] lemma toSuccPerm_apply {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1)) :
    toSuccPerm σ v = σ (σ⁻¹ v + 1) := by
  simp [toSuccPerm, Equiv.Perm.mul_apply, Equiv.addRight]

end TournamentHamiltonPaths
