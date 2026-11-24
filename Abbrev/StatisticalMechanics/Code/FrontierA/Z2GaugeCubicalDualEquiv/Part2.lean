module
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part4
open scoped symmDiff
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable section

abbrev CubicalDualVertex (a b c : Nat) := Option (CubicalCell a b c)


end
end StatMech.FrontierA
