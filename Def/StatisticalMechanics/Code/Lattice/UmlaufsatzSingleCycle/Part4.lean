/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part3
open SimpleGraph Function Set Finset


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


noncomputable def usc_localTurn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (f : Site 2) : ℤ :=
  ∑ i ∈ usc_visitSet K a f, turnZ K ((dartNext K)^[i] a.1)


noncomputable def usc_orbitFaces (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Finset (Site 2) := by
  classical
  exact (Finset.range (dartOrbitPeriod K a)).image (fun i => dartFace ((dartNext K)^[i] a.1))


end Lattice
end StatMech
