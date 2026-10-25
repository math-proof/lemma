/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Instance.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jeb_correctWhitney_imageGraph (P : PlanarZ2Subgraph)
    (p q f0 g0 : Site 2) (hpq : (hypercubicLattice 2).Adj p q)
    (hnpq : s(p, q) ∉ (imageGraph P).edgeSet) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) (imageGraph P).edgeSet.toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))) :
    ((imageGraph P).Reachable p q ↔
      ¬ ((whb_faceRegion (imageGraph P)).deleteEdges {s(f0, g0)}).Reachable f0 g0) :=
  jeb_correctWhitney_of_evenDegree (imageGraph P) (imageGraph_le_lattice P) p q f0 g0
    hpq hnpq hfg hshared hcc


end Lattice
end StatMech
