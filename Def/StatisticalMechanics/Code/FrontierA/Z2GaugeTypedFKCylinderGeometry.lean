/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

def finiteGeom (r : Real) (N : Nat) : Real :=
  ∑ d ∈ Finset.range N, r ^ d


end
end StatMech.FrontierA
