/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.Buildings.code.AffineCoxeter.PerronFrobeniusProof
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity.Part3
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic.Part4
set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- A Coxeter matrix is of **affine type** if its bilinear form is indecomposable, positive
semidefinite, and degenerate. Equivalently, it has Coxeter graph of affine Dynkin type. -/
def IsAffineCoxeter (M : CoxeterMatrix B) : Prop :=
  FormIndecomposable (fun s t => formVal M s t) ∧
  (∀ v : B → ℝ, bilinForm M v v ≥ 0) ∧
  (∃ v : B → ℝ, v ≠ 0 ∧ bilinForm M v v = 0)

/-- The **affine hyperplane** $E = \{\mu : \langle v_0, \mu\rangle = 1\}$ on which the affine Weyl
group acts. Here $v_0$ is the positive radical vector of the Coxeter form. -/
def affineHyperplane (_M : CoxeterMatrix B) (v₀ : B → ℝ) : Set (B → ℝ) :=
  {μ | ∑ s, v₀ s * μ s = 1}

