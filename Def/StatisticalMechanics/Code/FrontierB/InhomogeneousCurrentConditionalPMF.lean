/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness


noncomputable def inhomogeneousFiniteParityKernel
    {E : Type*} [DecidableEq E] (S : Finset E) (lambda : E -> Real)
    (odd : S -> Bool) (a : S -> Nat) : Real :=
  ∏ i, parityEdgeKernel (lambda i.1) (odd i) (a i)

end StatMech.FrontierB
