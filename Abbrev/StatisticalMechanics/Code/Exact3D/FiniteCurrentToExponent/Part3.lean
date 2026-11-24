module
public import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part136
public import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part7
public import Theorem.StatisticalMechanics.Code.Exact3D.ExponentTheorem
public import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.BcEqIsing
public import Theorem.StatisticalMechanics.Code.Ising.TransitionAssembly
public import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

noncomputable abbrev Ising3DFKBetaC : ℝ :=
  IsingFK.betaC (Ising.magnetization 3)

noncomputable abbrev Ising3DFKPC : ℝ :=
  IsingFK.pOfBeta Ising3DFKBetaC

end Exact3D
end StatMech
