/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising


noncomputable def nonnegativeFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (odd : ↑S → Bool) (a : ↑S → ℕ) : ℝ :=
  ∏ i, nonnegativeParityEdgeKernel (lambda i.1) (odd i) (a i)

end StatMech.FrontierB
