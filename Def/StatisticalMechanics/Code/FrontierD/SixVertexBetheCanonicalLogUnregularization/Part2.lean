module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLogRegularizationCutoff
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalRegularizedQuadrature
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalLogUnregularization.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularization.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexLogRegularizationSchedule (m : Nat) : Real :=
  1 / ((m : Real) + 1)

end
end StatMech.FrontierD
