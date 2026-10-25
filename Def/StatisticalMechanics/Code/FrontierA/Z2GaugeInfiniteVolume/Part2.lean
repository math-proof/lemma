/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part2
open Filter Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

def cubicalFixedLoopWilsonSequence (beta : Real) (a b n : Nat) : Real :=
  cubicalPaddedWilsonExpectation beta a b n n n n n n

end
end StatMech.FrontierA
