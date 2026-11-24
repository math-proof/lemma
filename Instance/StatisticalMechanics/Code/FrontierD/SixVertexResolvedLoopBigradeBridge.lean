module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedLoopBigradeBridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

instance instDecidablePropResolvedLoopBridge (p : Prop) : Decidable p :=
  Classical.propDecidable p

end
end StatMech.FrontierD
