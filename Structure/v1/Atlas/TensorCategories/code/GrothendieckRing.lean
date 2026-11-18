/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
public import Theorem.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Ring.Defs
public import Def.v1.Atlas.TensorCategories.code.GrothendieckRing
public section

set_option maxHeartbeats 800000

open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- Bundled form of the Grothendieck ring of a fusion ring `R`: an element is identified
with its integer-valued coefficient function on the basis. -/
@[ext]
structure GrRingOf (R : FusionRing ι) where
  coeff : ι → ℤ

end FusionRing
