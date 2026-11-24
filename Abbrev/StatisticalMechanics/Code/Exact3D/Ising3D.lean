module
public import Mathlib
public import Def.StatisticalMechanics.Code.Exact3D.CorrelationLength.Part3
public import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
public import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
public import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
open MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

open StatMech.Lattice


abbrev Ising3DSite : Type :=
  Site 3


end Exact3D
end StatMech
