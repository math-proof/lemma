/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalWitnessStep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
import Instance.StatisticalMechanics.Code.FrontierD.FKRectPrimalWitnessStep
open scoped BigOperators
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

theorem fkRectPrimalExploration_condMass_eq_freeUnexplored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace
      (Sym2 (FKRectPrimalUnexploredVertex R S eta)))) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
            ⁻¹' A).indicator (fun _ => (1 : Real)) rho *
          FK.condBcProb (fkRectCutGraph R)
            (StatMech.Lattice.boundaryCliqueGraph
              (fun _ : R.Vertex => False)) p q
            (fkRectPrimalUnexploredPairEdges R S eta)
            (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) rho) =
      ∑ omega : ConfigSpace
          (Sym2 (FKRectPrimalUnexploredVertex R S eta)),
        A.indicator (fun _ => (1 : Real)) omega *
          FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta)
            p q omega := by
  letI instInner : Fintype (FKRectPrimalUnexploredVertex R S eta) :=
    instFintypeFKRectPrimalUnexploredVertex R S eta
  let iota : FKRectPrimalUnexploredVertex R S eta → R.Vertex :=
    Subtype.val
  let psi : ConfigSpace (Sym2 R.Vertex) :=
    fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)
  simpa only [fkRectPrimalUnexploredPairEdges] using
    FK.ocd_condBcProb_innerEvent_eq_of_psiExt
    (Gin := fkRectPrimalUnexploredInducedGraph R S eta)
    (Gout := fkRectCutGraph R)
    (iota := iota)
    (bdryOut := fun _ : R.Vertex => False)
    Subtype.val_injective
    (fkRectPrimalUnexploredInducedGraph_adjMatch R S eta)
    hp hp1 hq psi
    (fun omega => FK.fkProb
      (fkRectPrimalUnexploredInducedGraph R S eta) p q omega)
    (fun omega => by
      simpa only [iota, psi] using
        fkRectPrimalExploration_condBcProb_eq_freeUnexplored
          R S eta hp hp1 hq omega)
    A


theorem fkRectPrimalExploration_condRightArm_le_boxBdry
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source : FKRectPrimalUnexploredVertex R S eta)
    (hleft : source.1.1 = fkRectLeftColumn R)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
            ⁻¹' FKRectPrimalUnexploredRightArmEvent R S eta source).indicator
              (fun _ => (1 : Real)) rho *
          FK.condBcProb (fkRectCutGraph R)
            (StatMech.Lattice.boundaryCliqueGraph
              (fun _ : R.Vertex => False)) p q
            (fkRectPrimalUnexploredPairEdges R S eta)
            (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) rho) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2)) := by
  rw [fkRectPrimalExploration_condMass_eq_freeUnexplored
    R S eta hp hp1 (zero_lt_one.trans_le hq)]
  exact fkRectPrimalUnexploredRightArm_freeMass_le_boxBdry
    R S eta source hleft hp hp1 hq


theorem fkRectPrimalUnexploredInducedGraph_adj_of_insert_reachable
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta)
    {x y : R.Vertex}
    (hix : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable
      (fkRectLeftColumn R, i) x)
    (hxy : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Adj x y) :
    let x' : FKRectPrimalUnexploredVertex R S eta :=
      ⟨x, fkRectPrimalCrossing_insert_cluster_disjoint_explored
        R eta S i hi hwitness hix⟩
    let y' : FKRectPrimalUnexploredVertex R S eta :=
      ⟨y, fkRectPrimalCrossing_insert_cluster_disjoint_explored
        R eta S i hi hwitness (hix.trans hxy.reachable)⟩
    (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta)
      (FK.ocd_innerRestrict
        (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
        (fkRectFullGraphConfiguration R
          (fkRectForceCutClosed R eta)))).Adj x' y' := by
  dsimp only
  rcases hxy with ⟨a, haopen, haedge⟩
  constructor
  · apply (fkRectCutGraph_adj_iff R x y).2
    constructor
    · exact ⟨a, haedge⟩
    · intro hcut
      have hacut : a ∈ fkRectTorusCutEdges R := by
        rw [← mem_fkRectTorusCutGraphEdges R a]
        simpa only [haedge] using hcut
      have hfalse := fkRectForceCutClosed_of_mem R eta a hacut
      rw [haopen] at hfalse
      exact Bool.noConfusion hfalse
  · have hopen : fkRectFullGraphConfiguration R
        (fkRectForceCutClosed R eta) s(x, y) = true := by
      rw [← haedge, fkRectFullGraphConfiguration_indexedEdge]
      exact haopen
    simpa [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk] using hopen


theorem fkRectPrimalUnexploredInduced_reachable_of_insert_reachable
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta)
    {v : R.Vertex}
    (hiv : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable
      (fkRectLeftColumn R, i) v) :
    let source : FKRectPrimalUnexploredVertex R S eta :=
      ⟨(fkRectLeftColumn R, i),
        fkRectPrimalCrossing_insert_source_not_explored
          R eta S i hi hwitness⟩
    let target : FKRectPrimalUnexploredVertex R S eta :=
      ⟨v, fkRectPrimalCrossing_insert_cluster_disjoint_explored
        R eta S i hi hwitness hiv⟩
    (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta)
      (FK.ocd_innerRestrict
        (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
        (fkRectFullGraphConfiguration R
          (fkRectForceCutClosed R eta)))).Reachable source target := by
  let sourceVertex : R.Vertex := (fkRectLeftColumn R, i)
  let G := fkRectOpenGraph R (fkRectForceCutClosed R eta)
  let H := FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta)
    (FK.ocd_innerRestrict
      (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
      (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)))
  let liftWalk : ∀ {x y : R.Vertex} (path : G.Walk x y)
      (hsx : G.Reachable sourceVertex x),
      H.Walk
        ⟨x, fkRectPrimalCrossing_insert_cluster_disjoint_explored
          R eta S i hi hwitness hsx⟩
        ⟨y, fkRectPrimalCrossing_insert_cluster_disjoint_explored
          R eta S i hi hwitness (hsx.trans path.reachable)⟩ := by
    intro x y path
    induction path with
    | nil =>
        intro hsx
        exact SimpleGraph.Walk.nil
    | @cons x y z hxy path ih =>
        intro hsx
        exact SimpleGraph.Walk.cons
          (fkRectPrimalUnexploredInducedGraph_adj_of_insert_reachable
            R eta S i hi hwitness hsx hxy)
          (ih (hsx.trans hxy.reachable))
  exact hiv.elim fun path => by
    refine ⟨?_⟩
    simpa only [sourceVertex, G, H] using
      liftWalk path (SimpleGraph.Reachable.refl sourceVertex)


theorem fkRectPrimalCrossingSourceWitnessCore_insert_imp_inducedRightArm
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta) :
    let source : FKRectPrimalUnexploredVertex R S eta :=
      ⟨(fkRectLeftColumn R, i),
        fkRectPrimalCrossing_insert_source_not_explored
          R eta S i hi hwitness⟩
    FK.ocd_innerRestrict
        (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) ∈
      FKRectPrimalUnexploredRightArmEvent R S eta source := by
  dsimp only
  have hrep : i ∈ fkRectRawHorizontalCrossingRepresentativeIndices R
      (fkRectForceCutClosed R eta) :=
    hwitness (Finset.mem_insert_self i S)
  obtain ⟨z, hiz⟩ :=
    fkRectRawHorizontalCrossingRepresentativeIndices_subset_sources
      R (fkRectForceCutClosed R eta) i hrep
  let target : FKRectPrimalUnexploredVertex R S eta :=
    ⟨(fkRectRightColumn R, z),
      fkRectPrimalCrossing_insert_cluster_disjoint_explored
        R eta S i hi hwitness hiz⟩
  refine ⟨target, rfl, ?_⟩
  exact fkRectPrimalUnexploredInduced_reachable_of_insert_reachable
    R eta S i hi hwitness hiz

end
end StatMech.FrontierD
