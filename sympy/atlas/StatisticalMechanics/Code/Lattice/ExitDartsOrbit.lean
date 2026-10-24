/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExitDartsOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import sympy.atlas.StatisticalMechanics.Code.Foundations.ConfigSpace
import sympy.atlas.StatisticalMechanics.Code.Lattice.HypercubicLattice
import sympy.atlas.StatisticalMechanics.Code.Lattice.PlanarDual
import sympy.atlas.StatisticalMechanics.Code.Lattice.Clusters
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanZ2
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanEnclosure
import sympy.atlas.StatisticalMechanics.Code.Lattice.PlanarTopology
import sympy.atlas.StatisticalMechanics.Code.Lattice.ContourAnchor
import sympy.atlas.StatisticalMechanics.Code.Lattice.EnclosingLength
import sympy.atlas.StatisticalMechanics.Code.Lattice.LeftFace
import sympy.atlas.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent
import sympy.atlas.StatisticalMechanics.Code.Lattice.BoundaryConnected
import sympy.atlas.StatisticalMechanics.Code.Lattice.DartDef
import sympy.atlas.StatisticalMechanics.Code.Lattice.DartNext
import sympy.atlas.StatisticalMechanics.Code.Lattice.DartInjective
import sympy.atlas.StatisticalMechanics.Code.Lattice.DartOrbit
import sympy.atlas.StatisticalMechanics.Code.Lattice.ContourLinksExits
import sympy.atlas.StatisticalMechanics.Code.Lattice.InterfaceOrbit

open Finset Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}














def exitDart_headSameComponent (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
    ⟨(exitDart (ω := ω) hfin).head, (exitDart_isBoundaryDart (ω := ω) hfin).2⟩
    ⟨(leftExitDart (ω := ω) hfin).head, (leftExitDart_isBoundaryDart (ω := ω) hfin).2⟩



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
