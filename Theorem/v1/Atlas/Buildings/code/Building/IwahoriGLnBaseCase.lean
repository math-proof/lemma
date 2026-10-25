/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnBaseCase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.IwahoriGLnDefs
import Def.v1.Atlas.Buildings.code.Building.IwahoriGLnHelpers
import Lemma.Fin.ValElimMatrix.eq.Transvection.of.Ne
import Mathlib.Tactic.FinCases
open Matrix


namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

end DVRContext
