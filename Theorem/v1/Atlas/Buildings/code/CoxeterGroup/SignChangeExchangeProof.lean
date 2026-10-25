/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignChangeExchangeProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterHomomorphism.Part2
import Structure.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionGenuine
import Mathlib.GroupTheory.Coxeter.Length
open Finset BigOperators CoxeterGroup CoxeterExchangeGenuine

set_option maxHeartbeats 0


namespace CoxeterSignChangeExchange

variable {B : Type*} [DecidableEq B] [Fintype B]

end CoxeterSignChangeExchange
