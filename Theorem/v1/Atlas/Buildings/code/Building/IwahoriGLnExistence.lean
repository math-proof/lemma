/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.IwahoriGLnBaseCase
import Lemma.Fin.Val.lt.Val.is.Eq_0AndEq_1
import Lemma.Finset.Sum_Mul.eq.Add_Sum_Mul.of.All_Eq_0.Eq_1
import Theorem.v1.Atlas.Buildings.code.Building.IwahoriGLnClearing
set_option maxHeartbeats 400000

open Matrix


namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

end DVRContext
