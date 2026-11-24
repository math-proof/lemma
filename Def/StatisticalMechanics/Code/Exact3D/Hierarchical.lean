module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
public import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
public import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

def hierarchicalScale : BlockScale where
  L := 2
  one_lt := by norm_num


def hierarchicalThermalEigenvalue : ℝ :=
  3


noncomputable def hierarchicalStableEigenvalue : ℝ :=
  (1 : ℝ) / 2

end Exact3D
end StatMech
