module
public import Mathlib
public import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part13


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


namespace PolymerSupport

def cubicTransformSite {d : ℕ} (v : Site d) (σ : Equiv.Perm (Fin d))
    (ε : CoordinateReflection d) (x : Site d) : Site d :=
  reflectCoordinatesSite ε (permuteCoordinatesSite σ x) + v

end PolymerSupport
end Exact3D
end StatMech
