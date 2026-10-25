/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GroupoidMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.GradedObject
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Algebra.Pi
import Structure.v1.Atlas.TensorCategories.code.GroupoidMultitensor
set_option maxHeartbeats 800000

open CategoryTheory

universe u v w


namespace GroupoidMultitensor

attribute [instance] FiniteGroupoidData.finObj FiniteGroupoidData.finMor

attribute [instance] FiniteGroupoidData.decEqObj FiniteGroupoidData.decEqMor

/-- The groupoid `G` has a single object (its object set has cardinality `1`). -/
def FiniteGroupoidData.IsSingleObject (G : FiniteGroupoidData) : Prop :=
  Fintype.card G.Obj = 1

/-- The number of objects of the finite groupoid `G`. -/
noncomputable def FiniteGroupoidData.numObjects (G : FiniteGroupoidData) : ℕ :=
  Fintype.card G.Obj

/-- The subtype of morphisms of `G` between two specified objects. -/
def FiniteGroupoidData.MorBetween (G : FiniteGroupoidData) (x y : G.Obj) : Type v :=
  { g : G.Mor // G.src g = y ∧ G.tgt g = x }

/-- The image of the identity map: the set of identity morphisms, one per object. -/
def FiniteGroupoidData.unitComponents (G : FiniteGroupoidData) : Finset G.Mor :=
  Finset.univ.image G.id

/-- The groupoid has a single connected component contributing to the unit, i.e. only one
identity morphism. -/
def FiniteGroupoidData.HasSimpleUnit (G : FiniteGroupoidData) : Prop :=
  G.unitComponents.card = 1

end GroupoidMultitensor
