/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.Potts.Part3
open scoped BigOperators


namespace StatMech

namespace Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in
theorem pottsWeight_pos {q : ℕ} (β J : ℝ) (σ : V → Fin q) : 0 < pottsWeight G β J σ :=
  Real.exp_pos _

omit [DecidableEq V] in
theorem pottsWeight_nonneg {q : ℕ} (β J : ℝ) (σ : V → Fin q) : 0 ≤ pottsWeight G β J σ :=
  (pottsWeight_pos G β J σ).le


end Potts
end StatMech
