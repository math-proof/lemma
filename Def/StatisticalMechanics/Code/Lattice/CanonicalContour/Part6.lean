/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CanonicalContour.Part5
open Finset Set SimpleGraph Function MeasureTheory
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin percolationEvent mem_percolationEvent)

variable {ω : ConfigSpace (Sym2 (Site 2))}


noncomputable def canonicalFaceWalk (hfin : (cluster 2 ω (origin 2)).Finite) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
      (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin) := by
  refine (canonicalFaceWalkAux (cluster 2 ω (origin 2)) (exitDart (ω := ω) hfin)
    (exitDart_isBoundaryDart (ω := ω) hfin)
    (dartOrbitPeriod (cluster 2 ω (origin 2))
      ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩)).copy
    (dartFace_exitDart (ω := ω) hfin) ?_
  
  have hret : (dartNext (cluster 2 ω (origin 2)))^[dartOrbitPeriod (cluster 2 ω (origin 2))
        ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩]
        (exitDart (ω := ω) hfin) = exitDart (ω := ω) hfin := by
    have := dartOrbitPeriod_iterate (cluster 2 ω (origin 2))
      ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩
    have h2 := congrArg Subtype.val this
    rwa [dartNextSub_iterate_val] at h2
  rw [hret, dartFace_exitDart (ω := ω) hfin]


end Lattice
end StatMech
