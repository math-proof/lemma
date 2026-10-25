/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.SimpleModule.Basic
import Instance.v1.Atlas.TensorCategories.code.DistinguishedInvertible.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.DistinguishedInvertible
set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section IntegralDefs

variable (R : Type u) [CommSemiring R] (H : Type v) [Semiring H] [Algebra R H] [Coalgebra R H]

/-- A left integral in an algebra `H` with counit is an element `I` satisfying
`x * I = ε(x) • I` for all `x ∈ H` (Definition 1.52.1). -/
structure IsLeftIntegral (I : H) : Prop where
  left_integral : ∀ (x : H), x * I = Coalgebra.counit (R := R) x • I

/-- A right integral in an algebra `H` with counit is an element `I` satisfying
`I * x = ε(x) • I` for all `x ∈ H` (Definition 1.52.1). -/
structure IsRightIntegral (I : H) : Prop where
  right_integral : ∀ (x : H), I * x = Coalgebra.counit (R := R) x • I

end IntegralDefs
