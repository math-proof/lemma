/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part16


namespace StatMech

namespace Exact3D

open StatMech.Lattice


structure PolymerSymmetryTag where
  translationQuotiented : Bool
  cubicQuotiented : Bool
  spinFlipEven : Bool


structure LocalPolymerCoordinate (d : ℕ) where
  support : PolymerSupport d
  degree : ℕ
  range : ℕ
  symmetry : PolymerSymmetryTag


structure LatticeRGData (d : ℕ) where
  H : EffectiveHamiltonian
  R : BlockSpinMap H
  kernel : BlockSpinKernel d
  scale_match : kernel.scale = R.scale

end Exact3D
end StatMech
