/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/CoxeterComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
import Mathlib.GroupTheory.Coxeter.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex
variable {B : Type*} [DecidableEq B] [Fintype B]


namespace CoxeterComplex

/-- A simplex in the Coxeter complex of $M$: a chamber representative $w \in W$ together with a
subset of simple generators determining the standard parabolic. -/
structure Simplex (M : CoxeterMatrix B) where
  rep : M.Group
  subset : Finset B

end CoxeterComplex
