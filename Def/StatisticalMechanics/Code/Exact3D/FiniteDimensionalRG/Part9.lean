module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
public import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplitting

def cone {n : ℕ} (_H : FiniteHyperbolicSplitting n)
    (η : ℝ) (x : State n) : Prop :=
  StableBlockWithRemainder.ThermalStableCone η x.1 x.2


end FiniteHyperbolicSplitting
end Exact3D
end StatMech
