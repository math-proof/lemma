/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
import Lemma.Nat.IsInO
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
open Matrix


namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

/-- *`DVRClosureGL2` axioms*: the structural closure properties of a DVR context needed to
prove the Iwahori decomposition for $GL_2$. Beyond the basic `DVRClosure`, we require: units
are nonzero, the maximal ideal absorbs products with elements of $\mathfrak{o}$, units are
closed under inversion, and a unit minus a maximal-ideal element is still a unit. -/
class DVRClosureGL2 (C : DVRContext) extends DVRClosure C where
  isUnitInO_ne_zero : ∀ {x : C.k}, C.isUnitInO x → x ≠ 0
  isInMaxIdeal_mul_isInO : ∀ {x y : C.k}, C.isInMaxIdeal x → C.isInO y → C.isInMaxIdeal (x * y)
  isUnitInO_inv_isUnitInO : ∀ {x : C.k}, C.isUnitInO x → C.isUnitInO x⁻¹
  isUnitInO_sub_isInMaxIdeal : ∀ {x y : C.k},
    C.isUnitInO x → C.isInMaxIdeal y → C.isUnitInO (x - y)

end DVRContext
