/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part5
import Theorem.StatisticalMechanics.Code.FK.FKQ2Sharp
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Walls.oc_boxobjects
open scoped BigOperators
open Finset Set
open scoped Classical

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace Walls

open StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]


structure oc_BoxFamily where
  
  theta : ℕ → ℝ → ℝ
  
  S : ℕ → ℝ → ℝ
  
  thetaDeriv : ℕ → ℝ → ℝ
  
  theta_nonneg : ∀ {β : ℝ}, 0 < β → β < 1 → ∀ n, 0 ≤ theta n β
  
  theta_le_one : ∀ {β : ℝ}, 0 < β → β < 1 → ∀ n, theta n β ≤ 1
  
  hasDerivAt_theta : ∀ {β : ℝ}, 0 < β → β < 1 → ∀ n,
    HasDerivAt (fun b => theta n b) (thetaDeriv n β) β
  
  theta_mono : ∀ n, ∀ {β₁ β₂ : ℝ}, 0 < β₁ → β₂ < 1 → β₁ ≤ β₂ → theta n β₁ ≤ theta n β₂
  
  S_succ : ∀ n β, S (n + 1) β = S n β + theta n β
  
  S_zero : ∀ β, S 0 β = 0


end Walls
end StatMech
