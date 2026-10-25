/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedMomentBridge.Part2
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

def scalarCumulantsOfMoments (moments : Nat -> Real) : Nat -> Real
  | 0 => 0
  | n + 1 => moments (n + 1) -
      ∑ k : Fin n, (n.choose k : Real) *
        scalarCumulantsOfMoments moments (k + 1) * moments (n - k)
termination_by order => order
decreasing_by omega

end
end StatMech.FrontierA
