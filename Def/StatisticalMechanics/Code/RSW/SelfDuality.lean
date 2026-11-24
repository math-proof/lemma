module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
open SimpleGraph Real


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace RSW

open StatMech.Lattice


def dualParam (p q pStar : ℝ) : Prop := p * pStar / ((1 - p) * (1 - pStar)) = q


noncomputable def selfDualPoint (q : ℝ) : ℝ := Real.sqrt q / (1 + Real.sqrt q)


end RSW
end StatMech
