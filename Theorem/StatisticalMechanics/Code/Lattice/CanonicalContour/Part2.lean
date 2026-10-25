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
import Def.StatisticalMechanics.Code.Lattice.CanonicalContour.Part2
open Finset Set SimpleGraph Function MeasureTheory
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin percolationEvent mem_percolationEvent)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem canonicalContour_length_eq (hfin : (cluster 2 ω (origin 2)).Finite) :
    (canonicalContour (ω := ω) hfin).length
      = dartOrbitPeriod (cluster 2 ω (origin 2))
          ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ :=
  dartOrbitWalk_length _ _


theorem canonicalContour_length_pos (hfin : (cluster 2 ω (origin 2)).Finite) :
    0 < (canonicalContour (ω := ω) hfin).length :=
  dartOrbitWalk_length_pos _ hfin _


theorem exitDart_tail_on_posAxis (hfin : (cluster 2 ω (origin 2)).Finite) :
    (exitDart (ω := ω) hfin).tail = ![(exitIndex (ω := ω) hfin : ℤ), 0] := by
  rw [exitDart_tail]; rfl


theorem orbitDart_isBoundaryDart (hfin : (cluster 2 ω (origin 2)).Finite) (n : ℕ) :
    IsBoundaryDart (cluster 2 ω (origin 2))
      ((dartNext (cluster 2 ω (origin 2)))^[n] (exitDart (ω := ω) hfin)) :=
  iterate_isBoundaryDart (cluster 2 ω (origin 2)) (exitDart (ω := ω) hfin)
    (exitDart_isBoundaryDart (ω := ω) hfin) n


theorem orbitDart_primalEdge_isClosed (hfin : (cluster 2 ω (origin 2)).Finite) (n : ℕ) :
    ω (dartPrimalEdge ((dartNext (cluster 2 ω (origin 2)))^[n] (exitDart (ω := ω) hfin)))
      = false :=
  boundaryDart_primalEdge_isClosed (origin 2) (orbitDart_isBoundaryDart (ω := ω) hfin n)


end Lattice
end StatMech
