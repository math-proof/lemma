module
public import Mathlib
public import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Structure.StatisticalMechanics.Code.Exact3D.LatticeRG


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

open StatMech.Lattice


def deterministicKernel {d : ℕ} (scale : BlockScale)
    (coarse : ConfigSpace (Site d) → ConfigSpace (BlockIndex d)) :
    BlockSpinKernel d where
  scale := scale
  allowed := fun σ τ => τ = coarse σ

end Exact3D
end StatMech
