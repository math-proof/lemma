/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/RootSignChangeProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterHomomorphism
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionGenuine
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.SigmaOrder
import Mathlib.GroupTheory.Coxeter.Inversion

open Finset BigOperators CoxeterGroup CoxeterExchangeGenuine

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace CoxeterRootSignChange

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Geometric root sign change hypothesis derived from the geometric bridge, packaging the
fact that the simple reflection $\sigma_s$ flips a positive root at the descent index. -/
noncomputable def rootSignChangeHyp {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (bridge : GeometricBridgeHyp M cs) :
    RootSignChangeHyp M cs where
  sign_change_at_index := by
    intro word s _k hred _hk hneg _hgt _hle


    exact bridge.sign_change_exchange word s hred hneg

end CoxeterRootSignChange
