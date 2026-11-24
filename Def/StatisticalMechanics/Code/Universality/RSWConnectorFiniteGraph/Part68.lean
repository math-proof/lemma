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
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part49
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

noncomputable def rlc_connectorSplitOuterEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (A : Set (ConfigSpace
      (rlc_connectorInnerGraph gamma gamma').edgeSet)) : Real :=
  (∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
      ∑ eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet,
        A.indicator (fun _ => (1 : Real)) eta *
          FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
            (rlc_connectorOuterDualConfig gamma gamma'
              (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) /
    rlc_connectorFibreMixtureZ gamma gamma' p q


end
end StatMech.Universality
