/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/Valuations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.NumberTheoryI.code.Chapter1.Valuations


noncomputable section

namespace DiscreteValuation

instance {k : Type*} [Field k] :
    FunLike (DiscreteValuation k) k (WithZero (Multiplicative ℤ)) where
  coe v := v.val
  coe_injective' := by
    intro v w h
    cases v; cases w
    simp only [mk.injEq]
    exact Valuation.ext (congrFun h)

instance {k : Type*} [Field k] :
    CoeOut (DiscreteValuation k) (Valuation k (WithZero (Multiplicative ℤ))) where
  coe v := v.val

end DiscreteValuation
end
