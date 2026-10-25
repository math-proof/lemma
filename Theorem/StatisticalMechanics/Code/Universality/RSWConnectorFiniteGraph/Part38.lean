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
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part26
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorInner_outerWeight_factorization {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcConnectorOuterDualVertex gamma gamma')))
    (omega : ConfigSpace
      (Sym2 (RlcConnectorInnerVertex gamma gamma')))
    (p q : Real) :
    FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma')
        (Lattice.boundaryCliqueGraph (fun _ => False)) p q
        (FK.ocd_psiExt (rlc_connectorInnerOuterVertex gamma gamma')
          psi omega) =
      FK.bcWeight (rlc_connectorInnerGraph gamma gamma')
          (rlc_connectorInnerInducedWiring gamma gamma' psi) p q omega *
        FK.ocd_psiShift (rlc_connectorOuterDualGraph gamma gamma')
          (rlc_connectorInnerOuterVertex gamma gamma')
          (fun _ => False) psi p q := by
  simpa [rlc_connectorInnerInducedWiring] using
    (FK.ocd_bcWeight_psiExt
      (Gin := rlc_connectorInnerGraph gamma gamma')
      (Gout := rlc_connectorOuterDualGraph gamma gamma')
      (ιV := rlc_connectorInnerOuterVertex gamma gamma')
      (bdryOut := fun _ => False)
      (rlc_connectorInnerOuterVertex_injective gamma gamma')
      (rlc_connectorInnerOuter_adjMatch gamma gamma')
      (p := p) (q := q) psi omega)


theorem rlc_connectorInner_condProb_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (psi : ConfigSpace
      (Sym2 (RlcConnectorOuterDualVertex gamma gamma')))
    (omega : ConfigSpace
      (Sym2 (RlcConnectorInnerVertex gamma gamma'))) :
    FK.condBcProb (rlc_connectorOuterDualGraph gamma gamma')
        (Lattice.boundaryCliqueGraph (fun _ => False)) p q
        (FK.ocd_innerEdgeFinset
          (rlc_connectorInnerOuterVertex gamma gamma')) psi
        (FK.ocd_psiExt (rlc_connectorInnerOuterVertex gamma gamma')
          psi omega) =
      FK.bcProb (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerInducedWiring gamma gamma' psi) p q omega := by
  simpa [rlc_connectorInnerInducedWiring] using
    (FK.ocd_condBcProb_psiExt_eq_bcProb
      (Gin := rlc_connectorInnerGraph gamma gamma')
      (Gout := rlc_connectorOuterDualGraph gamma gamma')
      (ιV := rlc_connectorInnerOuterVertex gamma gamma')
      (bdryOut := fun _ => False)
      (rlc_connectorInnerOuterVertex_injective gamma gamma')
      (rlc_connectorInnerOuter_adjMatch gamma gamma')
      hp hp1 hq psi omega)


end
end StatMech.Universality
