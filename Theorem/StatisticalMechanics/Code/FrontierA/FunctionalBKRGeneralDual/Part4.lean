/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneDual.Part3
import Theorem.StatisticalMechanics.Code.Walls.rb3reimerclose.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc4_core
import Theorem.StatisticalMechanics.Code.Walls.rc3_keyflipinvolutive
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part3
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.ConfigSpace

open StatMech.Walls

open StatMech.Walls.Reimer

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in

theorem dualPull_dualDisjointOccurrence {F : Type*} (e : E ≃ F)
    (A B : Set (ConfigSpace E)) :
    dualPull e (dualDisjointOccurrence A B) =
      dualDisjointOccurrence ((cfgEquiv e) ⁻¹' A) ((cfgEquiv e) ⁻¹' B) := by
  ext p
  constructor
  · rintro ⟨K, L, hKL, hA, hB⟩
    exact ⟨e '' K, e '' L, (Set.disjoint_image_iff e.injective).mpr hKL,
      (occursOn_cfgEquiv e A K p.1).mpr hA,
      (occursOn_cfgEquiv e B L p.2).mpr hB⟩
  · rintro ⟨K, L, hKL, hA, hB⟩
    refine ⟨e.symm '' K, e.symm '' L,
      (Set.disjoint_image_iff e.symm.injective).mpr hKL, ?_, ?_⟩
    · have h := (occursOn_cfgEquiv e A (e.symm '' K) p.1).mp
      rw [Set.image_image] at h
      simp only [Equiv.apply_symm_apply, Set.image_id'] at h
      exact h hA
    · have h := (occursOn_cfgEquiv e B (e.symm '' L) p.2).mp
      rw [Set.image_image] at h
      simp only [Equiv.apply_symm_apply, Set.image_id'] at h
      exact h hB


theorem dualWprob_transfer {F : Type*} [Fintype F] [DecidableEq F]
    (e : E ≃ F) (phi : E → Bool → ℝ)
    (C : Set (ConfigSpace E × ConfigSpace E)) :
    dualWprob phi C =
      dualWprob (fun y => phi (e.symm y)) (dualPull e C) := by
  unfold dualWprob
  rw [← Equiv.sum_comp (cfgEquiv e) (fun omega =>
    ∑ eta : ConfigSpace E,
      C.indicator (fun _ => (1 : ℝ)) (omega, eta) *
        (pweight phi omega * pweight phi eta))]
  apply Finset.sum_congr rfl
  intro omega _
  rw [← Equiv.sum_comp (cfgEquiv e) (fun eta =>
    C.indicator (fun _ => (1 : ℝ)) (cfgEquiv e omega, eta) *
      (pweight phi (cfgEquiv e omega) * pweight phi eta))]
  apply Finset.sum_congr rfl
  intro eta _
  rw [pweight_transfer, pweight_transfer]
  rfl


theorem dualBKR_wprob (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (A B : Set (ConfigSpace E)) :
    dualWprob phi (dualDisjointOccurrence A B) ≤ wprob phi (A ∩ B) := by
  classical
  set n := Fintype.card E
  obtain ⟨e⟩ := Fintype.truncEquivFin E
  set psi : Fin n → Bool → ℝ := fun y => phi (e.symm y)
  have hpsi0 : ∀ i b, 0 ≤ psi i b := fun i b => hphi0 (e.symm i) b
  have hpsi1 : ∀ i, psi i false + psi i true = 1 := fun i => hphi1 (e.symm i)
  have h := dualBKR_wprob_fin psi hpsi0 hpsi1
    ((cfgEquiv e) ⁻¹' A) ((cfgEquiv e) ⁻¹' B)
  rw [← dualPull_dualDisjointOccurrence e A B] at h
  rw [← dualWprob_transfer e phi (dualDisjointOccurrence A B)] at h
  have hinter :
      ((cfgEquiv e) ⁻¹' A) ∩ ((cfgEquiv e) ⁻¹' B) =
        (cfgEquiv e) ⁻¹' (A ∩ B) := by
    ext omega
    simp
  rw [hinter, ← wprob_transfer e phi (A ∩ B)] at h
  exact h


theorem dualFunctionalBKR_real (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (f g : ConfigSpace E → ℝ)
    (hf0 : ∀ omega, 0 ≤ f omega) (hg0 : ∀ omega, 0 ≤ g omega) :
    dualProductExpectation phi
        (fun pair => functionalDisjointMaxAt f g pair.1 pair.2) ≤
      productExpectation phi (fun omega => f omega * g omega) := by
  calc
    dualProductExpectation phi
        (fun pair => functionalDisjointMaxAt f g pair.1 pair.2) ≤
        ∑ omega : ConfigSpace E, ∑ eta : ConfigSpace E,
          pweight phi omega * pweight phi eta *
            (∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
              layerF.2 * layerG.2 *
                (dualDisjointOccurrence (realUpperLevel f layerF.1)
                  (realUpperLevel g layerG.1)).indicator
                    (fun _ => (1 : ℝ)) (omega, eta)) := by
      unfold dualProductExpectation
      apply Finset.sum_le_sum
      intro omega _
      apply Finset.sum_le_sum
      intro eta _
      exact mul_le_mul_of_nonneg_left
        (functionalDisjointMaxAt_real_le_dualLevels hf0 hg0 omega eta)
        (mul_nonneg (pweight_nonneg hphi0 omega) (pweight_nonneg hphi0 eta))
    _ = ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
          layerF.2 * layerG.2 *
            dualWprob phi
              (dualDisjointOccurrence (realUpperLevel f layerF.1)
                (realUpperLevel g layerG.1)) := by
      simp_rw [Finset.mul_sum]
      rw [kss_sum_four_comm (Finset.univ : Finset (ConfigSpace E))
        (Finset.univ : Finset (ConfigSpace E))
        (realLayerSet f) (realLayerSet g)]
      apply Finset.sum_congr rfl
      intro layerF _
      apply Finset.sum_congr rfl
      intro layerG _
      unfold dualWprob
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro omega _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro eta _
      ring
    _ ≤ ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
          layerF.2 * layerG.2 *
            wprob phi
              (realUpperLevel f layerF.1 ∩ realUpperLevel g layerG.1) := by
      apply Finset.sum_le_sum
      intro layerF hlayerF
      apply Finset.sum_le_sum
      intro layerG hlayerG
      apply mul_le_mul_of_nonneg_left
      · exact dualBKR_wprob phi hphi0 hphi1 _ _
      · exact mul_nonneg (realLayer_increment_nonneg hf0 hlayerF)
          (realLayer_increment_nonneg hg0 hlayerG)
    _ = productExpectation phi (fun omega => f omega * g omega) :=
      (productExpectation_real_mul_eq_levelIntersections phi hf0 hg0).symm

end StatMech.FrontierA
