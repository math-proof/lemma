/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part25
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorReflectedTraceEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  rlc_reflectedPathEdges gamma.1 ∪ rlc_reflectedPathEdges gamma'.1


noncomputable def rlc_connectorFourTraceEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
    rlc_connectorReflectedTraceEdges gamma gamma'


noncomputable def rlc_connectorReflectedTraceWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := (hypercubicLattice 2).Adj x.1 y.1 ∧
    s(x.1, y.1) ∈ rlc_connectorReflectedTraceEdges gamma gamma'
  symm := by
    constructor
    rintro x y ⟨hxy, hedge⟩
    exact ⟨hxy.symm, by simpa [Sym2.eq_swap] using hedge⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

end
end StatMech.Universality
