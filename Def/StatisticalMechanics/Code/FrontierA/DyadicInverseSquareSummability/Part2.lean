/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/DyadicInverseSquareSummability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Theorem.StatisticalMechanics.Code.FrontierA.DyadicInverseSquareSummability.Part2

@[expose] public section

open Filter Finset Set Topology


namespace StatMech.FrontierA

noncomputable section

def DyadicUpperFiber {Q : Type*} (size : Q → Real) (n : Nat) :=
  {q : Q // dyadicUpperLevel size q = n}

end
end StatMech.FrontierA
