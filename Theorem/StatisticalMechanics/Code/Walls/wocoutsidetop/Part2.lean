/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wocoutsidetop.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Def.StatisticalMechanics.Code.Walls.wocoutsidetop
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem woc_residue_eq (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) :
    woc_OutsideReachesExterior_residue Vc R ↔ oc_OutsideReachesExterior Vc R := Iff.rfl


theorem woc_reachesTop_of_residue (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (h : woc_OutsideReachesExterior_residue Vc R) :
    oc_OutsideReachesTop Vc R :=
  woc_reachesTop_of_reachesExterior Vc R hsupp h


theorem woc_residue_iff_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    woc_OutsideReachesExterior_residue Vc R ↔ oc_OutsideReachesTop Vc R :=
  (woc_reachesTop_iff_reachesExterior Vc R hsupp).symm


end Lattice
end StatMech
