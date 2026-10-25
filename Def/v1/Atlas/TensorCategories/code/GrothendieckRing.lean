/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
set_option maxHeartbeats 800000

open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- The underlying integer-valued function space `ι → ℤ` of the Grothendieck ring on basis
`ι`. Elements are interpreted as formal `ℤ`-linear combinations of basis vectors. -/
def GrRing (ι : Type*) [DecidableEq ι] [Fintype ι] := ι → ℤ

/-- Multiplication on `GrRing ι` defined by the fusion structure constants `N i j k`,
implementing `X_i X_j = ∑_k N_{ij}^k X_k`. -/
def grMul (f g : GrRing ι) : GrRing ι :=
  fun k => univ.sum fun i => univ.sum fun j => f i * g j * (R.N i j k : ℤ)

/-- The multiplicative identity of `GrRing ι`: the indicator function of the unit basis element. -/
def grOne : GrRing ι := fun k => if k = R.unit then 1 else 0

end FusionRing
