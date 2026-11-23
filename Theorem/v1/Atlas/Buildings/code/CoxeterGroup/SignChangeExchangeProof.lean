/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignChangeExchangeProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterHomomorphism.Part2
public import Structure.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionGenuine
public import Mathlib.GroupTheory.Coxeter.Length
open Finset BigOperators CoxeterGroup CoxeterExchangeGenuine

set_option maxHeartbeats 0

public section

namespace CoxeterSignChangeExchange

variable {B : Type*} [DecidableEq B] [Fintype B]

end CoxeterSignChangeExchange
