/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityOddInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFiniteSwitching


namespace StatMech.FrontierB

open Finset Sharpness

open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance currentContinuityOddInsertionPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p


end StatMech.FrontierB
