/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionWiring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.PosOfAscentProof
import Structure.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionGenuine
import Abbrev.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionWiring
open CoxeterGroup CoxeterExchangeGenuine

set_option maxHeartbeats 800000


namespace CoxeterExchange

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Deprecated bridge construction: builds the geometric bridge hypothesis
from a sign-change exchange hypothesis together with the length-decrease
implies negativity lemma. -/
@[deprecated "Use exchange_condition_unconditional from UnconditionalExchange.lean" (since := "2025-01-01")]
def geometricBridgeFromNegOfDescent {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (hsce : SignChangeExchangeHyp M cs) :
    GeometricBridgeHyp M cs where
  length_decrease_negative := neg_of_descent M cs
  sign_change_exchange := hsce

end CoxeterExchange
