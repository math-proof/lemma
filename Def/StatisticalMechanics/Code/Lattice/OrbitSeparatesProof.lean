/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedGlobal.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedBuild.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
import Theorem.StatisticalMechanics.Code.Lattice.OuterBoundarySingle.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


noncomputable def osp_windingRegion (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : Set (Site 2) :=
  jec_leftRegion (olb_orbitLoop K hK e he)

end Lattice
end StatMech
