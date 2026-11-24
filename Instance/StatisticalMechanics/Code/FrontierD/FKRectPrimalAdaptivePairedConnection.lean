module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalPairedConnection
open MeasureTheory SimpleGraph StatMech.Lattice


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

instance instDecidableFalseBoundaryAdaptivePaired (R : FKRectTorus) :
    DecidablePred (fun _ : R.Vertex => False) :=
  fun _ => isFalse id


end
end StatMech.FrontierD
