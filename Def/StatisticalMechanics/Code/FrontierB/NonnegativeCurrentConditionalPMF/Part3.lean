/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part2
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising


noncomputable def nonnegativeFiniteParityPMF
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E → ℝ)
    (hlambda : ∀ e : ↑S, 0 ≤ lambda e.1) (odd : ↑S → Bool) :
    PMF (↑S → ℕ) :=
  PMF.normalize
    (fun a => ENNReal.ofReal (nonnegativeFiniteParityKernel S lambda odd a))
    (by
      rw [tsum_ofReal_nonnegativeFiniteParityKernel S lambda hlambda odd]
      exact one_ne_zero)
    (by
      rw [tsum_ofReal_nonnegativeFiniteParityKernel S lambda hlambda odd]
      exact ENNReal.one_ne_top)

end StatMech.FrontierB
