/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalPairedConnection
import Instance.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptivePairedConnection
open MeasureTheory SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPrimalAdaptive_condMass_eq_freeUnexplored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (psi : ConfigSpace (Sym2 R.Vertex))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2
      (FKRectPrimalUnexploredVertex R S (fkRectCutConfigOfFull R psi).1)))) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectPrimalUnexploredVertex R S
            (fkRectCutConfigOfFull R psi).1 -> R.Vertex) ⁻¹' A).indicator
              (fun _ => (1 : Real)) rho *
          FK.condBcProb (fkRectCutGraph R)
            (boundaryCliqueGraph (fun _ : R.Vertex => False)) p q
            (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho) =
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        FK.fkProb (fkRectPrimalUnexploredInducedGraph R S
          (fkRectCutConfigOfFull R psi).1) p q omega := by
  let eta := fkRectCutConfigOfFull R psi
  let iota :=
    (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 -> R.Vertex)
  let psi0 := fkRectFullGraphConfiguration R eta.1
  have hforce : fkRectForceCutClosed R eta.1 = eta.1 := eta.2
  have hbot0 := fkRectPrimalExploration_ocdInducedWiring_eq_bot R S eta.1
  rw [hforce] at hbot0
  have hedgeEq : forall x y : R.Vertex, (fkRectCutGraph R).Adj x y ->
      psi s(x, y) = psi0 s(x, y) := by
    intro x y hxy
    have hedge : s(x, y) ∈ (fkRectCutGraph R).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact hxy
    have hclose := FK.ecz_closeOff_apply_edge (fkRectCutGraph R) psi hedge
    change psi s(x, y) =
      fkRectFullGraphConfiguration R (fkRectCutConfigOfFull R psi).1 s(x, y)
    rw [fkRectFullGraphConfiguration_cutConfigOfFull R psi]
    exact hclose.symm
  have hwiring :
      FK.ocd_inducedWiring (fkRectCutGraph R) iota
          (fun _ : R.Vertex => False) psi =
        (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta.1)) := by
    exact (FK.ocd_inducedWiring_congr_edges
      (fkRectCutGraph R) iota (fun _ : R.Vertex => False)
      psi psi0 hedgeEq).trans hbot0
  have hevent := FK.ocd_condBcProb_innerEvent_eq_of_psiExt
    (Gin := fkRectPrimalUnexploredInducedGraph R S eta.1)
    (Gout := fkRectCutGraph R)
    (iota := iota) (bdryOut := fun _ : R.Vertex => False)
    Subtype.val_injective
    (fkRectPrimalUnexploredInducedGraph_adjMatch R S eta.1)
    hp hp1 hq psi
    (fun omega => FK.fkProb
      (fkRectPrimalUnexploredInducedGraph R S eta.1) p q omega)
    (fun omega => by
      have hdm := FK.ocd_condBcProb_psiExt_eq_bcProb
        (Gin := fkRectPrimalUnexploredInducedGraph R S eta.1)
        (Gout := fkRectCutGraph R)
        (ιV := iota) (bdryOut := fun _ : R.Vertex => False)
        Subtype.val_injective
        (fkRectPrimalUnexploredInducedGraph_adjMatch R S eta.1)
        hp hp1 hq psi omega
      have hfree := @FK.bcProb_congr_boundary
        (FKRectPrimalUnexploredVertex R S eta.1)
        (instFintypeFKRectPrimalUnexploredVertex R S eta.1)
        (instDecidableEqFKRectPrimalUnexploredVertex R S eta.1)
        (fkRectPrimalUnexploredInducedGraph R S eta.1)
        (FK.ocd_inducedWiring (fkRectCutGraph R) iota
          (fun _ : R.Vertex => False) psi)
        (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta.1))
        (instDecidableRelPrimalUnexploredInducedGraph R S eta.1)
        (FK.instDecidableRelAdjOcd_inducedWiring _ _ _)
        (by infer_instance) hwiring p q omega
      rw [FK.bcProb_bot_eq_fkProb] at hfree
      exact hdm.trans hfree)
    A
  have hF : fkRectPrimalAdaptiveInsideEdges R S psi =
      fkRectPrimalUnexploredPairEdges R S eta.1 :=
    fkRectPrimalFullUnexploredPairEdges_eq_decoded R S psi
  rw [hF]
  simpa only [eta, iota] using hevent


end
end StatMech.FrontierD
