/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.GradedObject
import Mathlib.Tactic.Group
import Def.v1.Atlas.TensorCategories.code.GradedVec
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


/-- Objects of the twisted pointed monoidal category `Vec_G^ω`: a single
homogeneous component indexed by an element `val : G`. -/
@[ext]
structure CG (G : Type u) (A : Type v) [Monoid G] [CommGroup A]
    (_ω : NormalizedGroupCocycle3 G A) where
  val : G

/-- A morphism `X ⟶ Y` in `Vec_G^ω` exists only when `X.val = Y.val`,
and is the data of a single nonzero scalar `val : A`. -/
structure CG.Hom {G : Type u} {A : Type v} [Monoid G] [CommGroup A]
    {ω : NormalizedGroupCocycle3 G A} (X Y : CG G A ω) : Type v where
  val : A
  eq : X.val = Y.val

