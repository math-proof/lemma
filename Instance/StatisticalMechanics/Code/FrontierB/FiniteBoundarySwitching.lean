module
public import Theorem.StatisticalMechanics.Code.FrontierB.FiniteNormalizedSwitching
public import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundaryCurrentLaw.Part3
public import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentPairLaw.Part2
open scoped symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySwitching.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance boundarySwitchingPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p


end StatMech.FrontierB
