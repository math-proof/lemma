/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/InvariantPreserve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.OrbitBasis.Part4
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.OrbitBasis
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.LinearAlgebra.Finsupp.LSum
set_option autoImplicit false


noncomputable section

open scoped Classical Pointwise

open Finset Finsupp MulAction Function

namespace InvariantPreserve

variable (n : ℕ)

def upperCovers (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun T => S ⊂ T ∧ T.card = S.card + 1

def raisingOnBasis (S : Finset (Fin n)) : Finset (Fin n) →₀ ℝ :=
  (upperCovers n S).sum fun T => Finsupp.single T 1

def raisingOp : (Finset (Fin n) →₀ ℝ) →ₗ[ℝ] (Finset (Fin n) →₀ ℝ) :=
  Finsupp.lsum ℝ fun S => LinearMap.toSpanSingleton ℝ _ (raisingOnBasis n S)

def supportedAtLevel (i : ℕ) (v : Finset (Fin n) →₀ ℝ) : Prop :=
  ∀ S ∈ v.support, S.card = i

end InvariantPreserve
end
