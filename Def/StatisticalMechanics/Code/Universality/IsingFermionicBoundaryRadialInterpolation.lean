module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def isingLinearTent (x : Real) : Real := max 0 (1 - |x|)

end
end StatMech.Universality
