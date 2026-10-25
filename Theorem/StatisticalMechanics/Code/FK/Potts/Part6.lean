/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.Potts.Part6
open scoped BigOperators


namespace StatMech

namespace Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp]
theorem pottsPMF_apply (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    pottsPMF G q β J σ = ENNReal.ofReal (pottsProb G q β J σ) :=
  PMF.ofFintype_apply _ _

end Potts
end StatMech
