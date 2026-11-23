/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.StatisticalMechanics.Code.Inequalities.FKG

@[expose] public section

open Finset


namespace StatMech

namespace OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


def Agree (F : Finset E) (η ω : ConfigSpace E) : Prop := ∀ f ∈ F, ω f = η f

end OSSS.Monotonic
end StatMech
