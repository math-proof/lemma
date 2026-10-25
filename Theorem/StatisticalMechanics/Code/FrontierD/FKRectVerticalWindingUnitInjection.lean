/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingLevelPlateau.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryCompanionUnique
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectBlackBoundaryCycleInPrimalCluster_iff_component
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (C : FKRectConfigurationBlackBoundaryCycle R omega) :
    fkRectBlackBoundaryCycleInPrimalCluster R omega x C ↔
      fkRectBlackBoundaryCyclePrimalComponent R omega C =
        (fkRectOpenGraph R omega).connectedComponentMk x := by
  induction C using Quot.ind with
  | _ d =>
      rw [fkRectBlackBoundaryCycleInPrimalCluster_mk,
        fkRectBlackBoundaryCyclePrimalComponent_mk,
        ConnectedComponent.eq]
      exact ⟨fun h => h.symm, fun h => h.symm⟩


theorem fkRectBlackBoundaryCycleWinding_det_eq_zero_of_not_componentHasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (hnoNet : ¬ FKRectPrimalComponentHasNet R omega K)
    {C D : FKRectConfigurationBlackBoundaryCycle R omega}
    (hC : fkRectBlackBoundaryCycleInPrimalCluster R omega K.out C)
    (hD : fkRectBlackBoundaryCycleInPrimalCluster R omega K.out D) :
    (fkRectBlackBoundaryCycleWinding R omega C).1 *
          (fkRectBlackBoundaryCycleWinding R omega D).2 -
        (fkRectBlackBoundaryCycleWinding R omega C).2 *
          (fkRectBlackBoundaryCycleWinding R omega D).1 = 0 := by
  induction C using Quot.ind with
  | _ d =>
      induction D using Quot.ind with
      | _ e =>
          have hdK : (fkRectOpenGraph R omega).connectedComponentMk
              (fkRectMedialDartPrimalLabel R d.1) = K := by
            calc
              _ = fkRectBlackBoundaryCyclePrimalComponent R omega
                  (Quot.mk _ d) :=
                (fkRectBlackBoundaryCyclePrimalComponent_mk R omega d).symm
              _ = (fkRectOpenGraph R omega).connectedComponentMk K.out :=
                (fkRectBlackBoundaryCycleInPrimalCluster_iff_component
                  R omega K.out (Quot.mk _ d)).mp hC
              _ = K := K.out_eq
          have heK : (fkRectOpenGraph R omega).connectedComponentMk
              (fkRectMedialDartPrimalLabel R e.1) = K := by
            calc
              _ = fkRectBlackBoundaryCyclePrimalComponent R omega
                  (Quot.mk _ e) :=
                (fkRectBlackBoundaryCyclePrimalComponent_mk R omega e).symm
              _ = (fkRectOpenGraph R omega).connectedComponentMk K.out :=
                (fkRectBlackBoundaryCycleInPrimalCluster_iff_component
                  R omega K.out (Quot.mk _ e)).mp hD
              _ = K := K.out_eq
          by_contra hind
          apply hnoNet
          apply FKRectPrimalComponentHasNet.of_closedWalks R omega K
            hdK heK
            (fkRectBlackBoundaryPrimalCycleWalk R omega d)
            (fkRectBlackBoundaryPrimalCycleWalk R omega e)
          unfold FKRectWindingIndependent
          simpa only [fkRectBlackBoundaryCycleWinding_mk,
            ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
            using hind


theorem card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_sameSignUnique
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (hnoNet : ¬ FKRectPrimalComponentHasNet R omega K)
    (hsame : ∀ C D : FKRectConfigurationBlackBoundaryCycle R omega,
      C ∈ fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out →
      D ∈ fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out →
      (0 < (fkRectBlackBoundaryCycleWinding R omega C).1 *
          (fkRectBlackBoundaryCycleWinding R omega D).1 ∨
        0 < (fkRectBlackBoundaryCycleWinding R omega C).2 *
          (fkRectBlackBoundaryCycleWinding R omega D).2) →
      C = D) :
    (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2 := by
  classical
  let S := fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out
  by_cases hS : S.Nonempty
  · obtain ⟨C, hC⟩ := hS
    have hCspec : fkRectBlackBoundaryCycleInPrimalCluster R omega K.out C ∧
        fkRectBlackBoundaryCycleWinding R omega C ≠ 0 := by
      simpa [S, fkRectPrimalClusterNonzeroBoundaryCycles] using hC
    obtain ⟨D, hDC, hDcluster, hDne⟩ :=
      exists_other_nonzero_blackBoundaryCycle_in_primalCluster
        R omega K.out C hCspec.1 hCspec.2
    have hD : D ∈ S := by
      simp [S, fkRectPrimalClusterNonzeroBoundaryCycles, hDcluster, hDne]
    have hsub : S ⊆ {C, D} := by
      intro E hE
      by_cases hEC : E = C
      · simp [hEC]
      have hEspec : fkRectBlackBoundaryCycleInPrimalCluster R omega K.out E ∧
          fkRectBlackBoundaryCycleWinding R omega E ≠ 0 := by
        simpa [S, fkRectPrimalClusterNonzeroBoundaryCycles] using hE
      have hCDdet :=
        fkRectBlackBoundaryCycleWinding_det_eq_zero_of_not_componentHasNet
          R omega K hnoNet hCspec.1 hDcluster
      have hCEdet :=
        fkRectBlackBoundaryCycleWinding_det_eq_zero_of_not_componentHasNet
          R omega K hnoNet hCspec.1 hEspec.1
      let wC := fkRectBlackBoundaryCycleWinding R omega C
      let wD := fkRectBlackBoundaryCycleWinding R omega D
      let wE := fkRectBlackBoundaryCycleWinding R omega E
      have hDEsign : 0 < wD.1 * wE.1 ∨ 0 < wD.2 * wE.2 := by
        by_cases hCfst : wC.1 = 0
        · have hCsnd : wC.2 ≠ 0 := by
            intro h
            apply hCspec.2
            exact Prod.ext hCfst h
          have hDsnd : wD.2 ≠ 0 := by
            intro h
            have hDfst : wD.1 = 0 := by
              rw [hCfst, h] at hCDdet
              simp only [mul_zero, zero_sub] at hCDdet
              exact (mul_eq_zero.mp (neg_eq_zero.mp hCDdet)).resolve_left hCsnd
            apply hDne
            exact Prod.ext hDfst h
          have hEsnd : wE.2 ≠ 0 := by
            intro h
            have hEfst : wE.1 = 0 := by
              rw [hCfst, h] at hCEdet
              simp only [mul_zero, zero_sub] at hCEdet
              exact (mul_eq_zero.mp (neg_eq_zero.mp hCEdet)).resolve_left hCsnd
            apply hEspec.2
            exact Prod.ext hEfst h
          have hCDneg : wC.2 * wD.2 < 0 := by
            rcases lt_or_gt_of_ne (mul_ne_zero hCsnd hDsnd) with hneg | hpos
            · exact hneg
            · exact False.elim (hDC (hsame C D hC hD (Or.inr hpos)).symm)
          have hCEneg : wC.2 * wE.2 < 0 := by
            rcases lt_or_gt_of_ne (mul_ne_zero hCsnd hEsnd) with hneg | hpos
            · exact hneg
            · exact False.elim (hEC (hsame C E hC hE (Or.inr hpos)).symm)
          right
          rcases (mul_neg_iff.mp hCDneg) with h | h <;>
            rcases (mul_neg_iff.mp hCEneg) with h' | h'
          · exact mul_pos_of_neg_of_neg h.2 h'.2
          · exact (lt_asymm h.1 h'.1).elim
          · exact (lt_asymm h'.1 h.1).elim
          · exact mul_pos h.2 h'.2
        · have hDfst : wD.1 ≠ 0 := by
            intro h
            have hDsnd : wD.2 = 0 := by
              rw [h] at hCDdet
              simp only [mul_zero, sub_zero] at hCDdet
              exact (mul_eq_zero.mp hCDdet).resolve_left hCfst
            apply hDne
            exact Prod.ext h hDsnd
          have hEfst : wE.1 ≠ 0 := by
            intro h
            have hEsnd : wE.2 = 0 := by
              rw [h] at hCEdet
              simp only [mul_zero, sub_zero] at hCEdet
              exact (mul_eq_zero.mp hCEdet).resolve_left hCfst
            apply hEspec.2
            exact Prod.ext h hEsnd
          have hCDneg : wC.1 * wD.1 < 0 := by
            rcases lt_or_gt_of_ne (mul_ne_zero hCfst hDfst) with hneg | hpos
            · exact hneg
            · exact False.elim (hDC (hsame C D hC hD (Or.inl hpos)).symm)
          have hCEneg : wC.1 * wE.1 < 0 := by
            rcases lt_or_gt_of_ne (mul_ne_zero hCfst hEfst) with hneg | hpos
            · exact hneg
            · exact False.elim (hEC (hsame C E hC hE (Or.inl hpos)).symm)
          left
          rcases (mul_neg_iff.mp hCDneg) with h | h <;>
            rcases (mul_neg_iff.mp hCEneg) with h' | h'
          · exact mul_pos_of_neg_of_neg h.2 h'.2
          · exact (lt_asymm h.1 h'.1).elim
          · exact (lt_asymm h'.1 h.1).elim
          · exact mul_pos h.2 h'.2
      have hED : E = D := hsame E D hE hD (by
        rcases hDEsign with h | h
        · exact Or.inl (by simpa [wD, wE, mul_comm] using h)
        · exact Or.inr (by simpa [wD, wE, mul_comm] using h))
      simp [hED]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [show fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out = ∅ by
      simpa [S] using hzero]
    simp


theorem eq_of_sum_ite_eq_zero_of_card_nonzero_le_two_of_snd_mul_pos
    {D : Type*} [Fintype D]
    (p : D → Prop) [DecidablePred p] (w : D → Int × Int)
    (hsum : (∑ d : D, if p d then w d else 0) = 0)
    (hcard : (Finset.univ.filter fun d => p d ∧ w d ≠ 0).card ≤ 2)
    {a b : D} (ha : p a) (hb : p b)
    (hsign : 0 < (w a).2 * (w b).2) : a = b := by
  classical
  by_contra hab
  let S := Finset.univ.filter fun d => p d ∧ w d ≠ 0
  have hwa : w a ≠ 0 := by
    intro hzero
    rw [hzero] at hsign
    simp at hsign
  have hwb : w b ≠ 0 := by
    intro hzero
    rw [hzero] at hsign
    simp at hsign
  have haS : a ∈ S := by simp [S, ha, hwa]
  have hbS : b ∈ S := by simp [S, hb, hwb]
  have hpS : ({a, b} : Finset D) ⊆ S := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact haS
    · exact hbS
  have hcardS : S.card ≤ 2 := by simpa [S] using hcard
  have hpair : ({a, b} : Finset D) = S := by
    apply Finset.eq_of_subset_of_card_le hpS
    simpa [hab] using hcardS
  have hsumS : (∑ d ∈ S, w d) = 0 := by
    change (∑ d ∈ Finset.univ.filter (fun d => p d ∧ w d ≠ 0),
      w d) = 0
    rw [Finset.sum_filter]
    calc
      (∑ d : D, if p d ∧ w d ≠ 0 then w d else 0) =
          ∑ d : D, if p d then w d else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : p d <;> by_cases hw : w d = 0 <;> simp [hd, hw]
      _ = 0 := hsum
  rw [← hpair] at hsumS
  have hsnd := congrArg Prod.snd hsumS
  simp [hab] at hsnd
  have hbneg : (w b).2 = -(w a).2 := by omega
  rw [hbneg] at hsign
  nlinarith [sq_nonneg (w a).2]


theorem fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_snd_pos
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (hcard : (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card ≤ 2)
    {C D : FKRectConfigurationBlackBoundaryCycle R omega}
    (hC : fkRectBlackBoundaryCycleInPrimalCluster R omega x C)
    (hD : fkRectBlackBoundaryCycleInPrimalCluster R omega x D)
    (hCpos : 0 < (fkRectBlackBoundaryCycleWinding R omega C).2)
    (hDpos : 0 < (fkRectBlackBoundaryCycleWinding R omega D).2) :
    C = D := by
  classical
  apply eq_of_sum_ite_eq_zero_of_card_nonzero_le_two_of_snd_mul_pos
    (fun A : FKRectConfigurationBlackBoundaryCycle R omega =>
      fkRectBlackBoundaryCycleInPrimalCluster R omega x A)
    (fkRectBlackBoundaryCycleWinding R omega)
    (fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero R omega x)
    (by simpa [fkRectPrimalClusterNonzeroBoundaryCycles] using hcard)
    hC hD
  exact mul_pos hCpos hDpos


end
end StatMech.FrontierD
