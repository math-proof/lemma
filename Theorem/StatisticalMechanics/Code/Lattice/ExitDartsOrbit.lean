/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExitDartsOrbit.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Def.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem exitDart_headSameComponent_def (hfin : (cluster 2 ω (origin 2)).Finite) :
    exitDart_headSameComponent ω hfin
      ↔ ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
          ⟨(exitDart (ω := ω) hfin).head, (exitDart_isBoundaryDart (ω := ω) hfin).2⟩
          ⟨(leftExitDart (ω := ω) hfin).head, (leftExitDart_isBoundaryDart (ω := ω) hfin).2⟩ :=
  Iff.rfl


theorem exitDart_sameOrbit_imp_headSameComponent (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : ExitDartsSameOrbit ω hfin) : exitDart_headSameComponent ω hfin :=
  head_compl_of_exitDartsSameOrbit (ω := ω) hfin h


theorem exitDart_sameOrbit_of_headSameComponent (hfin : (cluster 2 ω (origin 2)).Finite)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (hcomp : exitDart_headSameComponent ω hfin) : ExitDartsSameOrbit ω hfin :=
  exitDartsSameOrbit_of_interfaceConnected (ω := ω) hfin hInt hcomp


theorem exitDart_sameOrbit_iff_headSameComponent (hfin : (cluster 2 ω (origin 2)).Finite)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2))) :
    ExitDartsSameOrbit ω hfin ↔ exitDart_headSameComponent ω hfin :=
  ⟨exitDart_sameOrbit_imp_headSameComponent (ω := ω) hfin,
    exitDart_sameOrbit_of_headSameComponent (ω := ω) hfin hInt⟩


theorem exitDart_headSameComponent_of_far (hfin : (cluster 2 ω (origin 2)).Finite)
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
    (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
    exitDart_headSameComponent ω hfin := by
  have hkey := exterior_reachable_in_compl (d := 2) (by norm_num)
    (cluster 2 ω (origin 2)) R hR hr hl
  exact complReachable_congr (G := hypercubicLattice 2) (S := (cluster 2 ω (origin 2))ᶜ)
    rfl rfl hkey


theorem exitDart_sameOrbit_of_far (hfin : (cluster 2 ω (origin 2)).Finite)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
    (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
    ExitDartsSameOrbit ω hfin :=
  exitDart_sameOrbit_of_headSameComponent (ω := ω) hfin hInt
    (exitDart_headSameComponent_of_far (ω := ω) hfin R hR hr hl)


end Lattice
end StatMech
