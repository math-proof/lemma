/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.Potts.Part2
open scoped BigOperators


namespace StatMech

namespace Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in
theorem agreement_nonneg {q : ℕ} (σ : V → Fin q) : 0 ≤ agreement G σ :=
  Finset.sum_nonneg fun e _ => monoIndicator_nonneg σ e


end Potts
end StatMech
