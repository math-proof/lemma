/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionWiring

open CoxeterExchange CoxeterGroup CoxeterExchangeGenuine

namespace StrongExchangeBridge

variable {W : Type*} [Group W] {B : Type*} [DecidableEq B] [Fintype B]
  {M : CoxeterMatrix B} {cs : CoxeterSystem M W}
