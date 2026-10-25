/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Lemma.Category.Atlas.v1.TensorCategories.code.BasedRings
import Abbrev.v1.Atlas.TensorCategories.code.BasedRings
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Def.v1.Atlas.TensorCategories.code.StarAlgebra
set_option maxHeartbeats 800000

open Finset Complex

attribute [instance] StarAlgWithTrace.instRing StarAlgWithTrace.instAlgebra
  StarAlgWithTrace.instStarRing StarAlgWithTrace.instStarModule


namespace StarAlgWithTrace

variable (B : StarAlgWithTrace)

noncomputable section

noncomputable section

/-- Proposition 1.43.4: the complexification of a (multifusion) based ring is canonically a
`*`-algebra: star is involutive, anti-multiplicative, the trace is symmetric, and the Hermitian
form is positive definite. -/
theorem Proposition_1_43_4 :

    (∀ f : ι → ℂ, R.grStarC' (R.grStarC' f) = f) ∧

    (∀ f g : ι → ℂ, R.grStarC' (R.grMulC' f g) = R.grMulC' (R.grStarC' g) (R.grStarC' f)) ∧

    (∀ a b : ι → ℂ, R.grTraceC' (R.grMulC' a b) = R.grTraceC' (R.grMulC' b a)) ∧

    (∀ a : ι → ℂ, a ≠ 0 → 0 < (R.grTraceC' (R.grMulC' a (R.grStarC' a))).re) :=
  ⟨R.grStarC'_invol, R.grStarC'_anti_mul, R.trace_comm_grC', R.trace_pos_def_grC'⟩

end
end
end StarAlgWithTrace
