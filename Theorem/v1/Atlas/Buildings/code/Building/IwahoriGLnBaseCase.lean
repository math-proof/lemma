module
public import Def.v1.Atlas.Buildings.code.Building.IwahoriGLnDefs
public import Def.v1.Atlas.Buildings.code.Building.IwahoriGLnHelpers
public import Theorem.Fin.ValElimMatrix.eq.Transvection.of.Ne
public import Mathlib.Tactic.FinCases
open Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnBaseCase.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

end DVRContext
