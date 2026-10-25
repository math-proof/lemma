/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebraExamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.CoradicalFiltration
import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part8
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Lie.UniversalEnveloping
import Class.v1.Atlas.TensorCategories.code.HopfAlgebraExamples.Part2
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v w


namespace TaftAlgebra

variable {k : Type u} [Field k] {A : Type v} [Ring A] [HopfAlgebra k A]
  [h : TaftAlgebra k A]

/-- The proposition that the Taft algebra is pointed as a coalgebra. -/
def isPointed_statement : Prop :=
  IsPointedCoalgebra (R := k) (C := A)

end TaftAlgebra
