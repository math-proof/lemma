module
public import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
public import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
public import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part18
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorComponentWiring {n : Int}
    (H : SimpleGraph (RlcConnectorVertex n)) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := x ≠ y ∧ H.Reachable x y
  symm := by
    constructor
    rintro x y ⟨hne, hxy⟩
    exact ⟨hne.symm, hxy.symm⟩
  loopless := ⟨fun x hxx => hxx.1 rfl⟩

end
end StatMech.Universality
