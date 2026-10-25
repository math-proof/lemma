/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.Potts.Part5
open scoped BigOperators


namespace StatMech

namespace Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem pottsProb_nonneg (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    0 ≤ pottsProb G q β J σ :=
  div_nonneg (pottsWeight_nonneg G β J σ) (pottsZ_pos G q β J).le


theorem pottsProb_pos (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    0 < pottsProb G q β J σ :=
  div_pos (pottsWeight_pos G β J σ) (pottsZ_pos G q β J)


theorem pottsProb_sum_eq_one (q : ℕ) [NeZero q] (β J : ℝ) :
    ∑ σ : V → Fin q, pottsProb G q β J σ = 1 := by
  unfold pottsProb
  rw [← Finset.sum_div]
  exact div_self (pottsZ_ne_zero G q β J)


end Potts
end StatMech
