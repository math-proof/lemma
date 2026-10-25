/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.Potts.Part5
open scoped BigOperators


namespace StatMech

namespace Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def pottsPMF (q : ℕ) [NeZero q] (β J : ℝ) : PMF (V → Fin q) :=
  PMF.ofFintype (fun σ => ENNReal.ofReal (pottsProb G q β J σ)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun σ _ => pottsProb_nonneg G q β J σ,
      pottsProb_sum_eq_one]
    simp

end Potts
end StatMech
