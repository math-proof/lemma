/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part5
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising


noncomputable def nonnegativeParityEdgeKernel
    (lambda : ℝ) (odd : Bool) (k : ℕ) : ℝ :=
  if lambda = 0 then if k = (if odd then 1 else 0) then 1 else 0
  else parityEdgeKernel lambda odd k

end StatMech.FrontierB
