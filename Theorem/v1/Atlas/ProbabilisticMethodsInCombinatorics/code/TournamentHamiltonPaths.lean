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
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.TournamentHamiltonPaths
set_option maxHeartbeats 3200000

open Real Finset BigOperators


namespace TournamentHamiltonPaths

attribute [instance] Tournament.decEdge

@[simp] lemma toSuccPerm_apply {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1)) :
    toSuccPerm σ v = σ (σ⁻¹ v + 1) := by
  simp [toSuccPerm, Equiv.Perm.mul_apply, Equiv.addRight]

end TournamentHamiltonPaths
