/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.CorrelationLength.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Abbrev.StatisticalMechanics.Code.Exact3D.Ising3D
open MeasureTheory


namespace StatMech

namespace Exact3D

open StatMech.Lattice


def ising3DLattice : SimpleGraph Ising3DSite :=
  hypercubicLattice 3


def ising3DOrigin : Ising3DSite :=
  0


def ising3DSiteOfCoords (x y z : ℤ) : Ising3DSite :=
  ![x, y, z]


def ising3DXAxisRay (n : ℕ) : Ising3DSite :=
  ising3DSiteOfCoords n 0 0


def ising3DYAxisRay (n : ℕ) : Ising3DSite :=
  ising3DSiteOfCoords 0 n 0


def ising3DZAxisRay (n : ℕ) : Ising3DSite :=
  ising3DSiteOfCoords 0 0 n


end Exact3D
end StatMech
