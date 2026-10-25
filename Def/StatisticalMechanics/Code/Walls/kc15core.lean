/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc15core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc14core.Part2
import Theorem.StatisticalMechanics.Code.Lattice.RotationSystemFaces.Part4
import Theorem.StatisticalMechanics.Code.Lattice.FacialSurjectivity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FacialSurjectivityProve
import Theorem.StatisticalMechanics.Code.Walls.kc15core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


def kc15_facialFamily (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) (x : Site 2) :
    Set (Set Dart) :=
  {{e : Dart | IsBoundaryDart (offSupportComponent Vc x) e},
   {e : Dart | IsBoundaryDart (offSupportComponent Vc (![-((R : ℤ) + 1), 0] : Site 2)) e}}


def kc15_FacialOrbitFamilyTwo (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) (x : Site 2) : Prop :=
  rsf_FacialOrbitsCoverComponents Vc (kc15_facialFamily Vc R x)


end Walls
end StatMech
