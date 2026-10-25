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
import Instance.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem fkRectPrimalAdaptive_condRightArm_le_boxBdry
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (psi : ConfigSpace (Sym2 R.Vertex))
    (source : FKRectPrimalUnexploredVertex R S
      (fkRectCutConfigOfFull R psi).1)
    (hleft : source.1.1 = fkRectLeftColumn R)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectPrimalUnexploredVertex R S
            (fkRectCutConfigOfFull R psi).1 → R.Vertex) ⁻¹'
          FKRectPrimalUnexploredRightArmEvent R S
            (fkRectCutConfigOfFull R psi).1 source).indicator
              (fun _ => (1 : Real)) rho *
          FK.condBcProb (fkRectCutGraph R)
            (StatMech.Lattice.boundaryCliqueGraph
              (fun _ : R.Vertex => False)) p q
            (fkRectPrimalFullUnexploredPairEdges R S psi) psi rho) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure (ConfigSpace
          (Sym2 (StatMech.Lattice.Site 2)))).real
        (FK.boxBdryConnEvent 2 (R.width - 2)) := by
  let eta := fkRectCutConfigOfFull R psi
  let iota :=
    (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 → R.Vertex)
  let psi0 := fkRectFullGraphConfiguration R eta.1
  let A := FKRectPrimalUnexploredRightArmEvent R S eta.1 source
  have hforce : fkRectForceCutClosed R eta.1 = eta.1 := eta.2
  have hbot0 := fkRectPrimalExploration_ocdInducedWiring_eq_bot R S eta.1
  rw [hforce] at hbot0
  have hedgeEq : ∀ x y : R.Vertex, (fkRectCutGraph R).Adj x y →
      psi s(x, y) = psi0 s(x, y) := by
    intro x y hxy
    have hedge : s(x, y) ∈ (fkRectCutGraph R).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact hxy
    have hclose := FK.ecz_closeOff_apply_edge
      (fkRectCutGraph R) psi hedge
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
    hp hp1 (zero_lt_one.trans_le hq) psi
    (fun omega => FK.fkProb
      (fkRectPrimalUnexploredInducedGraph R S eta.1) p q omega)
    (fun omega => by
      have hdm := FK.ocd_condBcProb_psiExt_eq_bcProb
        (Gin := fkRectPrimalUnexploredInducedGraph R S eta.1)
        (Gout := fkRectCutGraph R)
        (ιV := iota) (bdryOut := fun _ : R.Vertex => False)
        Subtype.val_injective
        (fkRectPrimalUnexploredInducedGraph_adjMatch R S eta.1)
        hp hp1 (zero_lt_one.trans_le hq) psi omega
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
  have hF : fkRectPrimalFullUnexploredPairEdges R S psi =
      fkRectPrimalUnexploredPairEdges R S eta.1 :=
    fkRectPrimalFullUnexploredPairEdges_eq_decoded R S psi
  rw [hF]
  change _ ≤ _
  rw [show (∑ rho : ConfigSpace (Sym2 R.Vertex),
      (FK.ocd_innerRestrict iota ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        FK.condBcProb (fkRectCutGraph R)
          (StatMech.Lattice.boundaryCliqueGraph
            (fun _ : R.Vertex => False)) p q
          (fkRectPrimalUnexploredPairEdges R S eta.1) psi rho) =
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta.1)
          p q omega by exact hevent]
  exact fkRectPrimalUnexploredRightArm_freeMass_le_boxBdry
    R S eta.1 source hleft hp hp1 hq


theorem fkRectPrimalAdaptiveArmEvent_condMass_le_boxBdry
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (psi : ConfigSpace (Sym2 R.Vertex))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (FKRectPrimalAdaptiveArmEvent R S i psi).indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb (fkRectCutGraph R)
            (StatMech.Lattice.boundaryCliqueGraph
              (fun _ : R.Vertex => False)) p q
            (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure (ConfigSpace
          (Sym2 (StatMech.Lattice.Site 2)))).real
        (FK.boxBdryConnEvent 2 (R.width - 2)) := by
  by_cases hsource : FKRectPrimalFullExploredVertex R S psi
      (fkRectLeftColumn R, i)
  · have hempty : FKRectPrimalAdaptiveArmEvent R S i psi = ∅ := by
      ext rho
      constructor
      · rintro ⟨hnot, _⟩
        exact (hnot hsource).elim
      · simp
    rw [hempty]
    simp only [Set.indicator_empty, zero_mul, Finset.sum_const_zero]
    exact MeasureTheory.measureReal_nonneg
  · let source : FKRectPrimalUnexploredVertex R S
        (fkRectCutConfigOfFull R psi).1 :=
      ⟨(fkRectLeftColumn R, i), fun h => hsource
        ((fkRectPrimalFullExploredVertex_iff R S psi _).2 h)⟩
    have hevent : FKRectPrimalAdaptiveArmEvent R S i psi =
        FK.ocd_innerRestrict
          (Subtype.val : FKRectPrimalUnexploredVertex R S
            (fkRectCutConfigOfFull R psi).1 → R.Vertex) ⁻¹'
          FKRectPrimalUnexploredRightArmEvent R S
            (fkRectCutConfigOfFull R psi).1 source := by
      ext rho
      constructor
      · rintro ⟨hnot, harm⟩
        simpa only [source] using harm
      · intro harm
        exact ⟨hsource, by simpa only [source] using harm⟩
    rw [hevent]
    exact fkRectPrimalAdaptive_condRightArm_le_boxBdry
      R S psi source rfl hp hp1 hq


theorem fkRectPrimalFullDistinctCrossingWitness_step
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (hi : i ∉ S)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho} ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure (ConfigSpace
          (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2)) *
        StatMech.Probability.finiteEventMass
          (FK.fkProb (fkRectCutGraph R) p q)
          {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} := by
  classical
  let P := fkRectPrimalAdaptiveProjection R S
  let Base : Set (ConfigSpace (Sym2 R.Vertex)) :=
    {rho | FKRectPrimalFullDistinctCrossingWitness R S rho}
  let Inserted : Set (ConfigSpace (Sym2 R.Vertex)) :=
    {rho | FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho}
  let Arm : ConfigSpace (Sym2 R.Vertex) →
      Set (ConfigSpace (Sym2 R.Vertex)) :=
    fun psi => FKRectPrimalAdaptiveArmEvent R S i psi
  let a := (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
    MeasureTheory.Measure (ConfigSpace
      (Sym2 (StatMech.Lattice.Site 2)))).real
      (FK.boxBdryConnEvent 2 (R.width - 2))
  apply StatMech.Probability.finiteEventMass_adaptive_fibre_step
    (FK.fkProb (fkRectCutGraph R) p q)
    (fun rho => FK.fkProb_nonneg (fkRectCutGraph R)
      hp hp1 (zero_lt_one.trans_le hq) rho)
    P
    (fun rho => fkRectPrimalAdaptiveProjection_idem R S rho)
    Base Inserted Arm
  · intro rho sigma hproj
    exact fkRectPrimalFullDistinctCrossingWitness_fibre_iff
      R S hproj
  · intro rho hrho
    exact ⟨fkRectPrimalFullDistinctCrossingWitness_insert_imp_base
        R S i rho hrho,
      fkRectPrimalFullDistinctCrossingWitness_insert_imp_adaptiveArm
        R S i hi rho hrho⟩
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
        FK.condBcProb (fkRectCutGraph R)
          (⊥ : SimpleGraph R.Vertex) p q F psi rho
    have hfilter : Finset.univ.filter (fun rho => P rho = psi) =
        FK.condFibre F psi := by
      exact fkRectPrimalAdaptiveProjection_filter_eq_condFibre
        R S psi hfixed
    have hraw := FK.bcProb_event_fibre_eq_mass_mul_cond
      (fkRectCutGraph R) (⊥ : SimpleGraph R.Vertex)
      hp hp1 (zero_lt_one.trans_le hq) F psi (Arm psi)
    simp_rw [FK.bcProb_bot_eq_fkProb] at hraw
    have hboundary : StatMech.Lattice.boundaryCliqueGraph
        (fun _ : R.Vertex => False) = (⊥ : SimpleGraph R.Vertex) := by
      apply SimpleGraph.ext
      ext x y
      rw [StatMech.Lattice.boundaryCliqueGraph_adj]
      simp [SimpleGraph.bot_adj]
    have hcond : C ≤ a := by
      simpa [C, a, hboundary] using
        fkRectPrimalAdaptiveArmEvent_condMass_le_boxBdry
          R S i psi hp hp1 hq
    have hM : 0 ≤ M := by
      exact Finset.sum_nonneg fun sigma _ =>
        FK.fkProb_nonneg (fkRectCutGraph R)
          hp hp1 (zero_lt_one.trans_le hq) sigma
    have hind : ∀ omega : ConfigSpace (Sym2 R.Vertex),
        (Arm psi).indicator (FK.fkProb (fkRectCutGraph R) p q) omega =
          FK.fkProb (fkRectCutGraph R) p q omega *
            (Arm psi).indicator (fun _ => (1 : Real)) omega := by
      intro omega
      by_cases hArm : omega ∈ Arm psi <;> simp [hArm]
    calc
      (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          (Arm psi).indicator (FK.fkProb (fkRectCutGraph R) p q) omega) =
        M * C := by
          rw [hfilter]
          simp_rw [hind]
          simpa [M, C, mul_comm] using hraw
      _ ≤ M * a := mul_le_mul_of_nonneg_left hcond hM
      _ = a * M := by ring
      _ = a * ∑ omega ∈
          (Finset.univ.filter fun omega => P omega = psi),
            FK.fkProb (fkRectCutGraph R) p q omega := by rw [hfilter]


end
end StatMech.FrontierD
