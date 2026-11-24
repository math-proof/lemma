module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
public import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.OutermostContour.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.PcFarContour
open Finset Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


open Classical in

noncomputable def fdc_rightExitIdx (_hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) : ℕ :=
  Nat.findGreatest (fun m => axisSite m ∈ cluster 2 ω (origin 2)) R


end Percolation
end StatMech
