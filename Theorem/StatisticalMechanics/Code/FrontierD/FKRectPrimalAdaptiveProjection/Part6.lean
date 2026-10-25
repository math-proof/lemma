/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalWitnessStep.Part2
import Theorem.StatisticalMechanics.Code.Probability.AdaptiveFibreStep
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part6
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (hi : i ∉ S)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho)
    {v : R.Vertex}
    (hiv : (FK.openSub (fkRectCutGraph R) rho).Reachable
      (fkRectLeftColumn R, i) v) :
    ¬ FKRectPrimalFullExploredVertex R S rho v := by
  rintro ⟨j, hj, hjv⟩
  apply h.2 i (Finset.mem_insert_self i S)
    j (Finset.mem_insert_of_mem hj) (fun hij => hi (hij ▸ hj))
  exact hiv.trans hjv.symm


theorem fkRectPrimalFullDistinctCrossingWitness_insert_imp_adaptiveArm
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (hi : i ∉ S)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho) :
    rho ∈ FKRectPrimalAdaptiveArmEvent R S i
      (fkRectPrimalAdaptiveProjection R S rho) := by
  let psi := fkRectPrimalAdaptiveProjection R S rho
  have hsourceRho :=
    fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable
      R S i hi rho h
        (SimpleGraph.Reachable.refl (fkRectLeftColumn R, i))
  have hsourcePsi : ¬ FKRectPrimalFullExploredVertex R S psi
      (fkRectLeftColumn R, i) := by
    intro hexplored
    exact hsourceRho
      ((fkRectPrimalFullExploredVertex_projection_iff R S rho _).1 hexplored)
  let eta := fkRectCutConfigOfFull R psi
  let source : FKRectPrimalUnexploredVertex R S eta.1 :=
    ⟨(fkRectLeftColumn R, i), fun hidx => hsourcePsi
      ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩
  rcases h.1 i (Finset.mem_insert_self i S) with ⟨z, hiz⟩
  have hnotPsi : ∀ {v : R.Vertex},
      (FK.openSub (fkRectCutGraph R) rho).Reachable
          (fkRectLeftColumn R, i) v →
        ¬ FKRectPrimalFullExploredVertex R S psi v := by
    intro v hiv hexplored
    have hexploredRho : FKRectPrimalFullExploredVertex R S rho v :=
      (fkRectPrimalFullExploredVertex_projection_iff R S rho v).1 hexplored
    exact fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable
      R S i hi rho h hiv hexploredRho
  let target : FKRectPrimalUnexploredVertex R S eta.1 :=
    ⟨(fkRectRightColumn R, z), fun hidx => hnotPsi hiz
      ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩
  have hreach :
      (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta.1)
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 → R.Vertex)
          rho)).Reachable source target := by
    let G := FK.openSub (fkRectCutGraph R) rho
    let H := FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta.1)
      (FK.ocd_innerRestrict
        (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 → R.Vertex)
        rho)
    let liftWalk : ∀ {x y : R.Vertex} (path : G.Walk x y)
        (hsx : G.Reachable (fkRectLeftColumn R, i) x),
        H.Walk
          ⟨x, fun hidx => hnotPsi hsx
            ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩
          ⟨y, fun hidx => hnotPsi (hsx.trans path.reachable)
            ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩ := by
      intro x y path
      induction path with
      | nil => intro _; exact SimpleGraph.Walk.nil
      | @cons x y z hxy path ih =>
          intro hsx
          have hstep : H.Adj
              ⟨x, fun hidx => hnotPsi hsx
                ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩
              ⟨y, fun hidx => hnotPsi (hsx.trans hxy.reachable)
                ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩ := by
            constructor
            · exact hxy.1
            · simpa [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk] using hxy.2
          exact SimpleGraph.Walk.cons hstep
            (ih (hsx.trans hxy.reachable))
    exact hiz.elim fun path =>
      ⟨by simpa only [source, target, G, H] using
        liftWalk path (SimpleGraph.Reachable.refl (fkRectLeftColumn R, i))⟩
  exact ⟨hsourcePsi, ⟨target, rfl, hreach⟩⟩


theorem fkRectPrimalFullDistinctCrossingWitness_insert_imp_base
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho) :
    FKRectPrimalFullDistinctCrossingWitness R S rho := by
  rcases h with ⟨hcross, hdistinct⟩
  exact ⟨fun j hj => hcross j (Finset.mem_insert_of_mem hj),
    fun j hj k hk hjk => hdistinct j (Finset.mem_insert_of_mem hj)
      k (Finset.mem_insert_of_mem hk) hjk⟩


theorem fkRectPrimalFullDistinctCrossingWitness_insert_source_not_explored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (hi : i ∉ S)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho) :
    ¬ FKRectPrimalFullExploredVertex R S rho (fkRectLeftColumn R, i) := by
  rintro ⟨j, hj, hji⟩
  exact h.2 i (Finset.mem_insert_self i S)
    j (Finset.mem_insert_of_mem hj) (fun hij => hi (hij ▸ hj)) hji.symm

end
end StatMech.FrontierD
