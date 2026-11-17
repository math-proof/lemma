/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
public import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
public import Structure.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part4

@[expose] public section


namespace StatMech

namespace Exact3D

namespace TwoCoordinateRGData

abbrev hamiltonian (_D : TwoCoordinateRGData) : EffectiveHamiltonian where
  carrier := ℝ × ℝ


end TwoCoordinateRGData
end Exact3D
end StatMech
