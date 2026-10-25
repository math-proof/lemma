/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpper.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond
open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Percolation

open StatMech.Lattice


noncomputable def primalEdgeFinset {u v : Site 2} (c : (hypercubicLattice 2).Walk u v) :
    Finset (Sym2 (Site 2)) :=
  (c.darts.map (fun D => sharedPrimalEdge D.fst D.snd)).toFinset


def closedCircuitEvent {u v : Site 2} (c : (hypercubicLattice 2).Walk u v) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | ∀ D ∈ c.darts, ω (sharedPrimalEdge D.fst D.snd) = false}


end Percolation
end StatMech
