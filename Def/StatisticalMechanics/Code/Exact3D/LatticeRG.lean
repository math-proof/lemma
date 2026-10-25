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
import Abbrev.StatisticalMechanics.Code.Exact3D.LatticeRG


namespace StatMech

namespace Exact3D

open StatMech.Lattice


def blockIndexOf {d : ℕ} (scale : BlockScale) (x : Site d) : BlockIndex d :=
  fun i => x i / (scale.L : ℤ)


def blockRepresentative {d : ℕ} (scale : BlockScale) (b : BlockIndex d) : Site d :=
  fun i => (scale.L : ℤ) * b i

end Exact3D
end StatMech
