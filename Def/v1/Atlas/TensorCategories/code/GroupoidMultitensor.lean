/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GroupoidMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Algebra.Pi
public import Structure.v1.Atlas.TensorCategories.code.GroupoidMultitensor

@[expose] public section

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
