/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionWiring
open CoxeterGroup CoxeterExchangeGenuine


namespace CoxeterExchange

variable {B : Type*} [DecidableEq B] [Fintype B]
  {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

end CoxeterExchange
