/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem exitFaces_reachable_of_sameOrbit (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : ExitDartsSameOrbit ω hfin) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Reachable
      (exitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) := by
  obtain ⟨n, hn⟩ := h
  have hr := dartFace_reachable_of_orbit (cluster 2 ω (origin 2))
    (exitDart (ω := ω) hfin) (leftExitDart (ω := ω) hfin)
    (exitDart_isBoundaryDart (ω := ω) hfin) hn
  rwa [dartFace_exitDart (ω := ω) hfin, dartFace_leftExitDart (ω := ω) hfin] at hr


theorem pc_lt_one_via_dartOrbit
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        EnclosingContourLinksExits ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  pc_lt_one_via_boundary h


end Lattice
end StatMech
