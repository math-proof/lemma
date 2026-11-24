module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerSeparation.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
public import Theorem.StatisticalMechanics.Code.Walls.jwd_contoureulerone
public import Theorem.StatisticalMechanics.Code.Walls.kc4_eulerone
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_eulerone.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


noncomputable def kc4_contourEulerChar (p : ℕ) : ℕ := contourEulerChar p


end Walls
end StatMech
