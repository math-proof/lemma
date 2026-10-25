/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteNormalizedSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteLocalSwitching.Part2
import Instance.StatisticalMechanics.Code.FrontierB.FiniteNormalizedSwitching
open scoped symmDiff


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def normalizedGatedSourcePairSum
    (beta : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (P : Current V → Prop) [DecidablePred P] : ℝ :=
  gatedSourcePairSum G beta J A B P /
    (currentSum G beta J A * currentSum G beta J B)


end StatMech.FrontierB
