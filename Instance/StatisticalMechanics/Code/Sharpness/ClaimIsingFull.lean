module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
public import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
public import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
public import Def.StatisticalMechanics.Code.Sharpness.ClaimIsingFull
open SimpleGraph Finset
open scoped BigOperators symmDiff
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


instance (S : Finset V) : DecidablePred (isIn G S) := fun i => by unfold isIn; infer_instance


end Sharpness
end StatMech
