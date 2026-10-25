/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part7
import Theorem.StatisticalMechanics.Code.Probability.FiniteWitnessUnionBound
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreFreeDomination.Part2
import Instance.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8


namespace StatMech.FrontierD

noncomputable section

theorem not_ocdOutsideGraph_adj_from_unexplored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (x : FKRectPrimalUnexploredVertex R S eta) (y : R.Vertex) :
    ¬ (FK.ocd_outsideGraph (fkRectCutGraph R)
      (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
      (fun _ : R.Vertex => False)
      (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))).Adj
        x.1 y := by
  intro hadj
  rw [FK.ocd_outsideGraph_adj] at hadj
  rcases hadj with hout | hboundary
  · rcases hout with ⟨hcut, hopen, hrange⟩
    have htorus : (fkRectTorusGraph R).Adj x.1 y :=
      (fkRectCutGraph_adj_iff R x.1 y).1 hcut |>.1
    obtain ⟨a, haedge⟩ :=
      (mem_fkRectTorusGraph_edgeSet_iff R s(x.1, y)).1
        ((SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).2 htorus)
    have hopenIndexed : fkRectForceCutClosed R eta a = true := by
      rw [← fkRectFullGraphConfiguration_indexedEdge R
        (fkRectForceCutClosed R eta) a, haedge]
      exact hopen
    have hopenAdj :
        (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Adj x.1 y :=
      ⟨a, hopenIndexed, haedge⟩
    by_cases hy : FKRectPrimalExploredVertex R S eta y
    · exact x.2 (fkRectPrimalExploredVertex_of_openAdj_right
        R S eta hopenAdj hy)
    · apply hrange
      let y' : FKRectPrimalUnexploredVertex R S eta := ⟨y, hy⟩
      refine ⟨s(x, y'), ?_⟩
      simp [FK.ocd_innerEdge, y']
  · exact hboundary.2.1.elim

theorem eq_of_ocdOutsideGraph_reachable_from_unexplored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {x y : R.Vertex}
    (hx : ¬ FKRectPrimalExploredVertex R S eta x)
    (hreach : (FK.ocd_outsideGraph (fkRectCutGraph R)
      (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
      (fun _ : R.Vertex => False)
      (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))).Reachable
        x y) :
    x = y := by
  exact hreach.elim fun p => by
    cases p with
    | nil => rfl
    | cons hstep rest =>
        exact False.elim
          (not_ocdOutsideGraph_adj_from_unexplored R S eta ⟨x, hx⟩ _ hstep)


theorem fkRectPrimalExploration_ocdInducedWiring_le_bot
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    FK.ocd_inducedWiring (fkRectCutGraph R)
        (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
        (fun _ : R.Vertex => False)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) ≤
      (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta)) := by
  intro x y hadj
  exfalso
  apply hadj.1
  exact Subtype.ext
    (eq_of_ocdOutsideGraph_reachable_from_unexplored
      R S eta x.2 hadj.2)

theorem fkRectPrimalExploration_ocdInducedWiring_eq_bot
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    FK.ocd_inducedWiring (fkRectCutGraph R)
        (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
        (fun _ : R.Vertex => False)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) =
      (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta)) := by
  exact le_antisymm
    (fkRectPrimalExploration_ocdInducedWiring_le_bot R S eta) bot_le


theorem fkRectPrimalExploration_condBcProb_eq_freeUnexplored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace
      (Sym2 (FKRectPrimalUnexploredVertex R S eta))) :
    FK.condBcProb (fkRectCutGraph R)
        (StatMech.Lattice.boundaryCliqueGraph
          (fun _ : R.Vertex => False)) p q
        (fkRectPrimalUnexploredPairEdges R S eta)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))
        (@FK.ocd_psiExt
          (FKRectPrimalUnexploredVertex R S eta) R.Vertex
          (instFintypeFKRectPrimalUnexploredVertex R S eta)
          (by infer_instance)
          (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
          (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) omega) =
      FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta) p q omega := by
  have hdm := FK.ocd_condBcProb_psiExt_eq_bcProb
    (Gin := fkRectPrimalUnexploredInducedGraph R S eta)
    (Gout := fkRectCutGraph R)
    (ιV := (Subtype.val :
      FKRectPrimalUnexploredVertex R S eta → R.Vertex))
    (bdryOut := fun _ : R.Vertex => False)
    Subtype.val_injective
    (fkRectPrimalUnexploredInducedGraph_adjMatch R S eta)
    hp hp1 hq
    (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) omega
  have hbot :
      FK.ocd_inducedWiring (fkRectCutGraph R)
          (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
          (fun _ : R.Vertex => False)
          (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) =
        (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta)) :=
    fkRectPrimalExploration_ocdInducedWiring_eq_bot R S eta
  have hfree := @FK.bcProb_congr_boundary
    (FKRectPrimalUnexploredVertex R S eta)
    (instFintypeFKRectPrimalUnexploredVertex R S eta)
    (instDecidableEqFKRectPrimalUnexploredVertex R S eta)
    (fkRectPrimalUnexploredInducedGraph R S eta)
    (FK.ocd_inducedWiring (fkRectCutGraph R)
      (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
      (fun _ : R.Vertex => False)
      (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)))
    (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta))
    (instDecidableRelPrimalUnexploredInducedGraph R S eta)
    (FK.instDecidableRelAdjOcd_inducedWiring _ _ _)
    (by infer_instance)
    hbot p q omega
  rw [FK.bcProb_bot_eq_fkProb] at hfree
  simpa only [fkRectPrimalUnexploredPairEdges] using hdm.trans hfree


theorem fkRectPrimalExploration_condFkProb_eq_induced
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta omega : R.Configuration) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.condFkProb (fkRectTorusGraph R) p q
        (fkRectPrimalUnexploredEdges R S eta)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))
        (fkRectFullGraphConfiguration R omega) =
      FK.inducedFkProb (fkRectTorusGraph R) p q
        (fkRectPrimalUnexploredEdges R S eta)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))
        (fkRectFullGraphConfiguration R omega) := by
  exact FK.condFkProb_eq_inducedFkProb
    (fkRectTorusGraph R) hp hp1 hq _ _ _


theorem exists_primalDualCrossingSourceWitness
    (R : FKRectTorus) (eta : R.Configuration) (n : Nat)
    (hclosed : FKRectCutClosedConfiguration R eta)
    (hn : n <=
      fkRectPrimalDualHorizontalCrossingClusterCount R eta) :
    exists S : Finset (Fin (2 * R.height)),
      S.card = n /\ FKRectPrimalDualCrossingSourceWitness R S eta := by
  classical
  let available :=
    fkRectPrimalDualCrossingRepresentativeSourceIndices R eta
  have hnAvailable : n <= available.card := by
    rw [card_fkRectPrimalDualCrossingRepresentativeSourceIndices]
    exact hn
  obtain ⟨S, hSsub, hScard⟩ :=
    Finset.exists_subset_card_eq hnAvailable
  exact ⟨S, hScard, hclosed, hSsub⟩


theorem fkRectCritical_primalDualCrossingTail_le_choose_mul_pow
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (n : Nat) (hn : 0 < n) (a : Real)
    (Witness : Finset (Fin (2 * R.height)) -> R.Configuration -> Prop)
    (hcover : forall eta : R.Configuration,
      FKRectCutClosedConfiguration R eta ->
        n <= fkRectPrimalDualHorizontalCrossingClusterCount R eta ->
        exists S : Finset (Fin (2 * R.height)),
          S.card = n /\ Witness S eta)
    (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n ->
      fkRectCriticalEventMass R q {eta | Witness S eta} <= a ^ n) :
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧ n <=
          fkRectPrimalDualHorizontalCrossingClusterCount R eta} <=
      Nat.choose (2 * R.height) n * a ^ n := by
  classical
  let K : R.Configuration -> Nat := fun eta =>
    if FKRectCutClosedConfiguration R eta then
      fkRectPrimalDualHorizontalCrossingClusterCount R eta else 0
  rw [fkRectCriticalEventMass_eq_finiteEventMass]
  have htail := StatMech.Probability.finiteEventMass_tail_le_choose_mul_pow
    (fun eta => fkRectCriticalRandomClusterProb R q eta)
    (fun eta => fkRectCriticalRandomClusterProb_nonneg R hq eta)
    K (2 * R.height) n a Witness (by
      intro eta heta
      by_cases hc : FKRectCutClosedConfiguration R eta
      · exact hcover eta hc (by simpa [K, hc] using heta)
      · simp [K, hc, Nat.not_le.mpr hn] at heta) (by
        intro S hS
        rw [<- fkRectCriticalEventMass_eq_finiteEventMass]
        exact hmass S hS)
  have hset : {eta : R.Configuration | n <= K eta} =
      {eta | FKRectCutClosedConfiguration R eta ∧
        n <= fkRectPrimalDualHorizontalCrossingClusterCount R eta} := by
    ext eta
    by_cases hc : FKRectCutClosedConfiguration R eta
    · simp [K, hc]
    · simp [K, hc, Nat.not_le.mpr hn]
  rw [<- hset]
  exact htail


theorem fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (n : Nat) (a : Real)
    (Witness : Finset (Fin (2 * R.height)) -> R.Configuration -> Prop)
    (hcover : forall eta : R.Configuration,
      FKRectCutClosedConfiguration R eta ->
        n < fkRectPrimalDualHorizontalCrossingClusterCount R eta ->
        exists S : Finset (Fin (2 * R.height)),
          S.card = n + 1 /\ Witness S eta)
    (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 ->
      fkRectCriticalEventMass R q {eta | Witness S eta} <= a ^ (n + 1)) :
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧ n <
          fkRectPrimalDualHorizontalCrossingClusterCount R eta} <=
      Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
  simpa only [Nat.lt_iff_add_one_le] using
    fkRectCritical_primalDualCrossingTail_le_choose_mul_pow
      R hq (n + 1) (Nat.succ_pos n) a Witness (by
        intro eta hclosed heta
        exact hcover eta hclosed (Nat.lt_iff_add_one_le.mpr heta)) hmass


theorem fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_sourceMass
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (n : Nat) (a : Real)
    (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 ->
      fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R S eta} <=
        a ^ (n + 1)) :
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧ n <
          fkRectPrimalDualHorizontalCrossingClusterCount R eta} <=
      Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
  apply fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow
    R hq n a (FKRectPrimalDualCrossingSourceWitness R)
  · intro eta hclosed heta
    exact exists_primalDualCrossingSourceWitness R eta (n + 1) hclosed
      (Nat.succ_le_of_lt heta)
  · exact hmass


theorem fkRectCritical_sourceWitnessMass_le_pow_of_step
    (R : FKRectTorus) {q : Real} (hq : 0 < q) {a : Real} (ha : 0 <= a)
    (hstep : forall (T : Finset (Fin (2 * R.height)))
      (i : Fin (2 * R.height)), i ∉ T ->
      fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} <=
        a * fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R T eta})
    (S : Finset (Fin (2 * R.height))) :
    fkRectCriticalEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitness R S eta} <=
      a ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      calc
        fkRectCriticalEventMass R q
            {eta | FKRectPrimalDualCrossingSourceWitness R ∅ eta} <=
          fkRectCriticalEventMass R q Set.univ :=
            fkRectCriticalEventMass_mono R hq (Set.subset_univ _)
        _ = 1 := by
          unfold fkRectCriticalEventMass
          simpa using sum_fkRectCriticalRandomClusterProb R hq
  | @insert i S hi ih =>
      calc
        fkRectCriticalEventMass R q
            {eta | FKRectPrimalDualCrossingSourceWitness R (insert i S) eta} <=
          a * fkRectCriticalEventMass R q
            {eta | FKRectPrimalDualCrossingSourceWitness R S eta} :=
          hstep S i hi
        _ <= a * a ^ S.card := mul_le_mul_of_nonneg_left ih ha
        _ = a ^ (insert i S).card := by
          rw [Finset.card_insert_of_notMem hi, pow_succ]
          ring


theorem fkRectCritical_sourceWitnessStep_of_cutFreeStep
    (R : FKRectTorus) {q : Real} (hq : 1 <= q) (a : Real)
    (hstep : forall (T : Finset (Fin (2 * R.height)))
      (i : Fin (2 * R.height)), i ∉ T ->
      fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitnessCore R (insert i T) eta} <=
        a * fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta})
    (T : Finset (Fin (2 * R.height)))
    (i : Fin (2 * R.height)) (hi : i ∉ T) :
    fkRectCriticalEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} <=
      a * fkRectCriticalEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitness R T eta} := by
  let Z := fkRectCriticalClosedMass R q (fkRectTorusCutEdges R)
  have hZ : 0 <= Z := (fkRectCriticalClosedMass_cut_pos R hq).le
  calc
    fkRectCriticalEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} =
      Z * fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitnessCore R (insert i T) eta} := by
          symm
          simpa [Z, FKRectPrimalDualCrossingSourceWitness] using
            closedMass_mul_fkRectCriticalCutFreeEventMass R hq
              {eta | FKRectPrimalDualCrossingSourceWitnessCore R
                (insert i T) eta}
    _ <= Z * (a * fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta}) :=
      mul_le_mul_of_nonneg_left (hstep T i hi) hZ
    _ = a * (Z * fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta}) := by ring
    _ = a * fkRectCriticalEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitness R T eta} := by
          congr 1
          simpa [Z, FKRectPrimalDualCrossingSourceWitness] using
            closedMass_mul_fkRectCriticalCutFreeEventMass R hq
              {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta}


theorem fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_step
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (n : Nat) {a : Real} (ha : 0 <= a)
    (hstep : forall (T : Finset (Fin (2 * R.height)))
      (i : Fin (2 * R.height)), i ∉ T ->
      fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} <=
        a * fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R T eta}) :
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧
          n < fkRectPrimalDualHorizontalCrossingClusterCount R eta} <=
      Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
  apply
    fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_sourceMass
      R hq n a
  intro S hS
  simpa only [hS] using
    fkRectCritical_sourceWitnessMass_le_pow_of_step R hq ha hstep S


theorem fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_cutFreeStep
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (n : Nat) {a : Real} (ha : 0 <= a)
    (hstep : forall (T : Finset (Fin (2 * R.height)))
      (i : Fin (2 * R.height)), i ∉ T ->
      fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitnessCore R (insert i T) eta} <=
        a * fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta}) :
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧
          n < fkRectPrimalDualHorizontalCrossingClusterCount R eta} <=
      Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
  apply fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_step
    R (lt_of_lt_of_le zero_lt_one hq) n ha
  intro T i hi
  exact fkRectCritical_sourceWitnessStep_of_cutFreeStep
    R hq a hstep T i hi

end
end StatMech.FrontierD
