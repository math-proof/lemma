module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingFull.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
public import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
public import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part3
open SimpleGraph Finset
open scoped BigOperators symmDiff
open Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean -/
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


open FluxEdgeCopy


def edgesIn (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (edgeInside S)


end Sharpness
end StatMech
