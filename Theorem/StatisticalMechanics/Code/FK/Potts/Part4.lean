/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.Potts.Part4
open scoped BigOperators


namespace StatMech

namespace Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem pottsZ_pos (q : ℕ) [NeZero q] (β J : ℝ) : 0 < pottsZ G q β J :=
  Finset.sum_pos (fun σ _ => pottsWeight_pos G β J σ) Finset.univ_nonempty

theorem pottsZ_ne_zero (q : ℕ) [NeZero q] (β J : ℝ) : pottsZ G q β J ≠ 0 :=
  (pottsZ_pos G q β J).ne'


end Potts
end StatMech
