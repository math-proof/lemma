module
public import Theorem.StatisticalMechanics.Code.Inequalities.FKG
public import Def.StatisticalMechanics.Code.OSSS.Monotonic
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


instance (F : Finset E) (η ω : ConfigSpace E) : Decidable (Agree F η ω) := by
  unfold Agree; infer_instance

end OSSS.Monotonic
end StatMech
