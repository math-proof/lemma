/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityFiniteSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.SwitchingDichotomy.Part2
open scoped symmDiff


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance currentContinuityFiniteSwitchingPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p


end StatMech.FrontierB
