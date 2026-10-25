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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part43
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorSourceActiveEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet ≃
      ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet ×
        ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma') where
  toFun tau := (rlc_connectorInnerActiveOfSource gamma gamma' tau,
    rlc_connectorOuterActiveOfSource gamma gamma' tau)
  invFun := rlc_connectorSourceActiveAssemble gamma gamma'
  left_inv tau := by
    funext e
    unfold rlc_connectorSourceActiveAssemble
    split
    · rename_i h
      have he : rlc_connectorInnerSourceEdge gamma gamma' h.choose = e :=
        h.choose_spec
      simp [rlc_connectorInnerActiveOfSource, he]
    · rename_i h
      rfl
  right_inv pair := by
    rcases pair with ⟨eta, xi⟩
    apply Prod.ext
    · funext e
      simp [rlc_connectorInnerActiveOfSource]
    · funext e
      simp [rlc_connectorOuterActiveOfSource]

end
end StatMech.Universality
