/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalPairedConnection
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptivePairedConnection.Part2
open MeasureTheory SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem FKRectPrimalFullDistinctPairedWitness.toDistinctCrossing
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctPairedWitness R pair S rho) :
    FKRectPrimalFullDistinctCrossingWitness R S rho := by
  exact ⟨fun i hi => ⟨pair i, h.1 i hi⟩, h.2⟩


theorem fkRectPrimalFullDistinctPairedWitness_projection_iff
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (rho : ConfigSpace (Sym2 R.Vertex)) :
    FKRectPrimalFullDistinctPairedWitness R pair S
        (fkRectPrimalAdaptiveProjection R S rho) <->
      FKRectPrimalFullDistinctPairedWitness R pair S rho := by
  constructor
  · rintro ⟨hpair, hdistinct⟩
    exact ⟨fun i hi =>
        (fkRectPrimalSourceReachable_projection_iff
          R S rho hi _).1 (hpair i hi),
      fun i hi j hj hij hreach => hdistinct i hi j hj hij
        ((fkRectPrimalSourceReachable_projection_iff
          R S rho hi _).2 hreach)⟩
  · rintro ⟨hpair, hdistinct⟩
    exact ⟨fun i hi =>
        (fkRectPrimalSourceReachable_projection_iff
          R S rho hi _).2 (hpair i hi),
      fun i hi j hj hij hreach => hdistinct i hi j hj hij
        ((fkRectPrimalSourceReachable_projection_iff
          R S rho hi _).1 hreach)⟩

theorem fkRectPrimalFullDistinctPairedWitness_fibre_iff
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height))
    {rho sigma : ConfigSpace (Sym2 R.Vertex)}
    (hproj : fkRectPrimalAdaptiveProjection R S rho =
      fkRectPrimalAdaptiveProjection R S sigma) :
    FKRectPrimalFullDistinctPairedWitness R pair S rho <->
      FKRectPrimalFullDistinctPairedWitness R pair S sigma := by
  rw [← fkRectPrimalFullDistinctPairedWitness_projection_iff
      R pair S rho,
    ← fkRectPrimalFullDistinctPairedWitness_projection_iff
      R pair S sigma,
    hproj]


theorem fkRectPrimalFullDistinctPairedWitness_insert_imp_base
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctPairedWitness R pair (insert i S) rho) :
    FKRectPrimalFullDistinctPairedWitness R pair S rho := by
  exact ⟨fun j hj => h.1 j (Finset.mem_insert_of_mem hj),
    fun j hj k hk hjk => h.2 j (Finset.mem_insert_of_mem hj)
      k (Finset.mem_insert_of_mem hk) hjk⟩


theorem fkRectPrimalFullDistinctPairedWitness_insert_imp_adaptiveConnection
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (i : Fin R.height) (hi : i ∉ S)
    (rho : ConfigSpace (Sym2 R.Vertex))
    (h : FKRectPrimalFullDistinctPairedWitness R pair (insert i S) rho) :
    rho ∈ FKRectPrimalAdaptivePairedConnectionEvent R S i (pair i)
      (fkRectPrimalAdaptiveProjection R S rho) := by
  let psi := fkRectPrimalAdaptiveProjection R S rho
  have hdistinct := h.toDistinctCrossing R pair (insert i S) rho
  have hreach := h.1 i (Finset.mem_insert_self i S)
  have hsourceRho : ¬ FKRectPrimalFullExploredVertex R S rho
      (fkRectLeftColumn R, i) :=
    fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable
      R S i hi rho hdistinct (SimpleGraph.Reachable.refl _)
  have htargetRho : ¬ FKRectPrimalFullExploredVertex R S rho
      (fkRectRightColumn R, pair i) :=
    fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable
      R S i hi rho hdistinct hreach
  have hsourcePsi : ¬ FKRectPrimalFullExploredVertex R S psi
      (fkRectLeftColumn R, i) := by
    intro hexplored
    exact hsourceRho
      ((fkRectPrimalFullExploredVertex_projection_iff R S rho _).1 hexplored)
  have htargetPsi : ¬ FKRectPrimalFullExploredVertex R S psi
      (fkRectRightColumn R, pair i) := by
    intro hexplored
    exact htargetRho
      ((fkRectPrimalFullExploredVertex_projection_iff R S rho _).1 hexplored)
  let eta := fkRectCutConfigOfFull R psi
  let source : FKRectPrimalUnexploredVertex R S eta.1 :=
    ⟨(fkRectLeftColumn R, i), fun hidx => hsourcePsi
      ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩
  let target : FKRectPrimalUnexploredVertex R S eta.1 :=
    ⟨(fkRectRightColumn R, pair i), fun hidx => htargetPsi
      ((fkRectPrimalFullExploredVertex_iff R S psi _).2 hidx)⟩
  have hnotPsi : forall {v : R.Vertex},
      (FK.openSub (fkRectCutGraph R) rho).Reachable
          (fkRectLeftColumn R, i) v ->
        ¬ FKRectPrimalFullExploredVertex R S psi v := by
    intro v hiv hexplored
    have hexploredRho : FKRectPrimalFullExploredVertex R S rho v :=
      (fkRectPrimalFullExploredVertex_projection_iff R S rho v).1 hexplored
    exact fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable
      R S i hi rho hdistinct hiv hexploredRho
  have hinduced :
      (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta.1)
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 -> R.Vertex)
          rho)).Reachable source target := by
    let G := FK.openSub (fkRectCutGraph R) rho
    let H := FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta.1)
      (FK.ocd_innerRestrict
        (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 -> R.Vertex)
        rho)
    let liftWalk : forall {x y : R.Vertex} (path : G.Walk x y)
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
            exact ⟨hxy.1, by
              simpa [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk] using hxy.2⟩
          exact SimpleGraph.Walk.cons hstep
            (ih (hsx.trans hxy.reachable))
    exact hreach.elim fun path =>
      ⟨by simpa only [source, target, G, H] using
        liftWalk path (SimpleGraph.Reachable.refl (fkRectLeftColumn R, i))⟩
  exact ⟨hsourcePsi, htargetPsi, hinduced⟩


theorem fkRectPrimalFullDistinctPairedWitness_step
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (i : Fin R.height) (hi : i ∉ S)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | FKRectPrimalFullDistinctPairedWitness
          R pair (insert i S) rho} <=
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxConnEvent 2 (R.width + R.height)
            (fkRectVertexBoxEmbedding R (fkRectLeftColumn R, i))
            (fkRectVertexBoxEmbedding R (fkRectRightColumn R, pair i))) *
        StatMech.Probability.finiteEventMass
          (FK.fkProb (fkRectCutGraph R) p q)
          {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} := by
  classical
  let P := fkRectPrimalAdaptiveProjection R S
  let Base : Set (ConfigSpace (Sym2 R.Vertex)) :=
    {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho}
  let Inserted : Set (ConfigSpace (Sym2 R.Vertex)) :=
    {rho | FKRectPrimalFullDistinctPairedWitness R pair (insert i S) rho}
  let Arm : ConfigSpace (Sym2 R.Vertex) ->
      Set (ConfigSpace (Sym2 R.Vertex)) := fun psi =>
    FKRectPrimalAdaptivePairedConnectionEvent R S i (pair i) psi
  let a := (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site 2)))).real
      (FK.boxConnEvent 2 (R.width + R.height)
        (fkRectVertexBoxEmbedding R (fkRectLeftColumn R, i))
        (fkRectVertexBoxEmbedding R (fkRectRightColumn R, pair i)))
  apply StatMech.Probability.finiteEventMass_adaptive_fibre_step
    (FK.fkProb (fkRectCutGraph R) p q)
    (fun rho => FK.fkProb_nonneg (fkRectCutGraph R)
      hp hp1 (zero_lt_one.trans_le hq) rho)
    P (fun rho => fkRectPrimalAdaptiveProjection_idem R S rho)
    Base Inserted Arm
  · intro rho sigma hproj
    exact fkRectPrimalFullDistinctPairedWitness_fibre_iff
      R pair S hproj
  · intro rho hrho
    exact ⟨fkRectPrimalFullDistinctPairedWitness_insert_imp_base
        R pair S i rho hrho,
      fkRectPrimalFullDistinctPairedWitness_insert_imp_adaptiveConnection
        R pair S i hi rho hrho⟩
  · intro psi hpsiImage
    obtain ⟨rho, _, hrho⟩ := Finset.mem_image.mp hpsiImage
    have hfixed : P psi = psi := by
      rw [← hrho]
      exact fkRectPrimalAdaptiveProjection_idem R S rho
    let F := fkRectPrimalAdaptiveInsideEdges R S psi
    let M := ∑ sigma ∈ FK.condFibre F psi,
      FK.fkProb (fkRectCutGraph R) p q sigma
    let C := ∑ rho,
      (Arm psi).indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb (fkRectCutGraph R) (⊥ : SimpleGraph R.Vertex)
          p q F psi rho
    have hfilter : Finset.univ.filter (fun rho => P rho = psi) =
        FK.condFibre F psi :=
      fkRectPrimalAdaptiveProjection_filter_eq_condFibre R S psi hfixed
    have hraw := FK.bcProb_event_fibre_eq_mass_mul_cond
      (fkRectCutGraph R) (⊥ : SimpleGraph R.Vertex)
      hp hp1 (zero_lt_one.trans_le hq) F psi (Arm psi)
    simp_rw [FK.bcProb_bot_eq_fkProb] at hraw
    have hboundary : boundaryCliqueGraph (fun _ : R.Vertex => False) =
        (⊥ : SimpleGraph R.Vertex) := by
      apply SimpleGraph.ext
      ext x y
      rw [boundaryCliqueGraph_adj]
      simp [SimpleGraph.bot_adj]
    have hcond : C <= a := by
      simpa [C, a, hboundary, Arm] using
        fkRectPrimalAdaptivePairedConnectionEvent_condMass_le_boxConn
          R S i (pair i) psi hp hp1 hq
    have hM : 0 <= M := Finset.sum_nonneg fun sigma _ =>
      FK.fkProb_nonneg (fkRectCutGraph R)
        hp hp1 (zero_lt_one.trans_le hq) sigma
    have hind : forall omega : ConfigSpace (Sym2 R.Vertex),
        (Arm psi).indicator (FK.fkProb (fkRectCutGraph R) p q) omega =
          FK.fkProb (fkRectCutGraph R) p q omega *
            (Arm psi).indicator (fun _ => (1 : Real)) omega := by
      intro omega
      by_cases hArm : omega ∈ Arm psi <;> simp [hArm]
    calc
      (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          (Arm psi).indicator
            (FK.fkProb (fkRectCutGraph R) p q) omega) = M * C := by
        rw [hfilter]
        simp_rw [hind]
        simpa [M, C, mul_comm] using hraw
      _ <= M * a := mul_le_mul_of_nonneg_left hcond hM
      _ = a * M := by ring
      _ = a * ∑ omega ∈
          (Finset.univ.filter fun omega => P omega = psi),
            FK.fkProb (fkRectCutGraph R) p q omega := by rw [hfilter]


end
end StatMech.FrontierD
