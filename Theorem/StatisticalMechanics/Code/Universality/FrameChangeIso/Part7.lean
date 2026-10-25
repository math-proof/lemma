/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Def.StatisticalMechanics.Code.Universality.FrameChangeIso.Part6
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem fci_faceEdgeEquiv_mk_of_adj {f g : Site 2}
    (h : (hypercubicLattice 2).Adj f g) :
    fci_faceEdgeEquiv s(f, g) = sharedPrimalEdge f g := by
  change (if _h : s(f, g) ∈ (hypercubicLattice 2).edgeSet then
    (fci_latticeEdgeEquiv ⟨s(f, g), _h⟩ : Sym2 (Site 2)) else s(f, g)) = _
  rw [dif_pos ((SimpleGraph.mem_edgeSet _).mpr h)]
  change fci_sharedEdgeRaw s(f, g) = sharedPrimalEdge f g
  exact fci_sharedEdgeRaw_mk_of_adj h


end Universality
end StatMech
