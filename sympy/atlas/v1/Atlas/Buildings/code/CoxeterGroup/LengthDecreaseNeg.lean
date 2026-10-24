/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/LengthDecreaseNeg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.WordSigmaInvariance
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.SimpleReflectionInversions
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionGenuine
import Mathlib.GroupTheory.Coxeter.Length

set_option maxHeartbeats 400000

open Finset BigOperators CoxeterGroup CoxeterExchangeGenuine

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


end CoxeterGroup
