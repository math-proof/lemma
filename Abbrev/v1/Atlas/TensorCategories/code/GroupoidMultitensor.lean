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
import Def.v1.Atlas.TensorCategories.code.GroupoidMultitensor
set_option maxHeartbeats 800000

open CategoryTheory

universe u v w


namespace GroupoidMultitensor

attribute [instance] FiniteGroupoidData.finObj FiniteGroupoidData.finMor

attribute [instance] FiniteGroupoidData.decEqObj FiniteGroupoidData.decEqMor

/-- The algebra of endomorphisms of the unit object for the groupoid-graded `k`-vector space
category: pointwise scalars indexed by objects of `G`. -/
abbrev FiniteGroupoidData.EndUnit (G : FiniteGroupoidData) (k : Type w) [Field k] :=
  G.Obj → k

end GroupoidMultitensor
