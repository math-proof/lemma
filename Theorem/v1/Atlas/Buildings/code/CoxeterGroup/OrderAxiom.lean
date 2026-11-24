module
public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.SigmaOrder
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.OrderAxiom
open CoxeterGroup


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/OrderAxiom.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

set_option linter.unusedSectionVars false

/-- Cons unfolding of `sigmaWord`. -/
@[simp] theorem sigmaWord_cons (M : CoxeterMatrix B) (s : B) (w : List B) :
    sigmaWord M (s :: w) = sigmaLin M s * sigmaWord M w := rfl

end CoxeterGroup
