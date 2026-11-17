/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part2


public section

namespace StatMech

namespace Exact3D

open StatMech.Lattice


structure BlockSpinKernel (d : ℕ) where
  scale : BlockScale
  allowed : ConfigSpace (Site d) → ConfigSpace (BlockIndex d) → Prop


end Exact3D
end StatMech
