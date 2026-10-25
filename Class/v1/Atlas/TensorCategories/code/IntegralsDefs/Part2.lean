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
import Def.v1.Atlas.TensorCategories.code.IntegralsDefs.Part2
set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section Proposition_1_52_4

open CategoryTheory

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]

/-- Categorical data needed to state Proposition 1.52.4: a procedure constructing
the one dimensional representation associated to a character, plus the agreement
between the distinguished invertible object and that representation. -/
class Prop1524Data
    (C : Type*) [Category C] [MonoidalCategory C] [RigidCategory C]
    [HasDistinguishedInvertibleData C] [FiniteDimensional k H] where
  oneDimChar : (H →ₗ[k] k) → C
  lρ_iso_distinguishedChar :
    ∀ (I : H) (_hI : I ≠ 0) (dc : DistinguishedCharacter k H I),
      Nonempty (HasDistinguishedInvertibleData.distinguished (C := C) ≅ oneDimChar dc.χ)

end Proposition_1_52_4
