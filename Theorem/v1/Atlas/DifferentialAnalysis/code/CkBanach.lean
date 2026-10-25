/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanach.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Normed.Group.Basic
open scoped ZeroAtInfty
open Filter Topology Finset


noncomputable section

set_option maxRecDepth 4000

namespace TestFunctions

variable {n : ℕ}

/-- The forgetful map from `ContDiffZeroAtInfty` to `ZeroAtInftyContinuousMap`
is injective: an element of the former is determined by its underlying
continuous map. -/
lemma ContDiffZeroAtInfty.toC0_injective :
    Function.Injective (ContDiffZeroAtInfty.toZeroAtInftyContinuousMap (n := n)) := by
  intro ⟨a, _, _⟩ ⟨b, _, _⟩ h; congr

/-- If for each direction `j` the partial derivative of `f` agrees with a
function `g j` that vanishes at infinity, then the partial derivative of `f`
itself vanishes at infinity. -/
lemma tendsto_partialDeriv_of_fderiv_eq
    (f : ZeroAtInftyContinuousMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (g : Fin n → EuclideanSpace ℝ (Fin n) → ℂ)
    (heq : ∀ j x, fderiv ℝ (⇑f) x (EuclideanSpace.single j 1) = g j x)
    (htend : ∀ j, Tendsto (g j) (cocompact _) (𝓝 0)) (j : Fin n) :
    Tendsto (fun x => fderiv ℝ (⇑f) x (EuclideanSpace.single j 1))
      (cocompact _) (𝓝 0) := by
  have : (fun x => fderiv ℝ (⇑f) x (EuclideanSpace.single j 1)) = g j :=
    funext (heq j)
  rw [this]; exact htend j

end TestFunctions
end
