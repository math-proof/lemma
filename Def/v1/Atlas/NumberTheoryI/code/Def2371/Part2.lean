/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Def2371.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.Thm2370
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Instance.v1.Atlas.NumberTheoryI.code.Def2371
open CategoryTheory CochainComplex HomComplex Abelian

universe w v u


section ModuleCat

variable (R : Type u) [Ring R] [Small.{v} R]

noncomputable def ExtGroup_R (M A : ModuleCat.{v} R) (n : ℕ) : Type v :=
  ExtGroup M A n

end ModuleCat
