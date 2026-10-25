/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part3
import Def.StatisticalMechanics.Code.FrontierB.CurrentLimitTranslation.Part3
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Ising Lattice Sharpness


theorem currentShiftLaw_apply {E H : Type*} [Countable E]
    [Group H] [MulAction H E] (g : H)
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (A : Set (InfiniteCurrentConfig E)) (hA : MeasurableSet A) :
    (currentShiftLaw g mu : Measure (InfiniteCurrentConfig E)) A =
      (mu : Measure (InfiniteCurrentConfig E)) ((currentShift g) ⁻¹' A) := by
  exact Measure.map_apply (measurable_currentShift g) hA


theorem currentParityMarginalPMF_currentShiftLaw_eq
    (d : Nat) (mu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (g : Multiplicative (Site d))
    (havoid : ∀ F : Finset (Sym2 (Site d)),
      (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet ->
      (mu : Measure _) ((currentShift g) ⁻¹'
          currentParityAvoidCylinder F) =
        (mu : Measure _) (currentParityAvoidCylinder F))
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    currentParityMarginalPMF (currentShiftLaw g mu) S =
      currentParityMarginalPMF mu S := by
  apply PMF.ext_of_boolAvoid_eq
  intro T
  rw [currentParityMarginalPMF_avoid, currentParityMarginalPMF_avoid]
  rw [currentShiftLaw_apply]
  · exact havoid (ambientSubfinset S T)
      (ambientSubfinset_lattice d S hS T)
  · have hset := currentParityAvoidCylinder_eq_currentCylinder
      (ambientSubfinset S T)
    rw [hset]
    exact measurableSet_currentCylinder _ _


theorem currentLimit_isTranslationInvariant
    (d : Nat) (beta : Real) (hbeta : 0 < beta)
    (mu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet ->
      (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | m e = 0} = 1)
    (hfactor : ∀ (S : Finset (Sym2 (Site d))),
      (↑S : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet ->
      ∀ a : ↑S -> Nat,
        (mu : Measure _) (currentCylinder S {a}) =
          (mu : Measure _)
              (currentParityPatternCylinder S (currentLocalParity a)) *
            finiteParityPMF S beta hbeta (currentLocalParity a) a)
    (havoid : ∀ (g : Multiplicative (Site d))
      (F : Finset (Sym2 (Site d))),
      (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet ->
      (mu : Measure _) ((currentShift g) ⁻¹'
          currentParityAvoidCylinder F) =
        (mu : Measure _) (currentParityAvoidCylinder F)) :
    CurrentIsTranslationInvariant (H := Multiplicative (Site d))
      (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
  intro g
  let rho := currentShiftLaw g mu
  have hrhoZero : ∀ e, e ∉ (hypercubicLattice d).edgeSet ->
      (rho : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | m e = 0} = 1 := by
    intro e he
    rw [currentShiftLaw_apply]
    · have hpre : (currentShift g) ⁻¹'
          {m : InfiniteCurrentConfig (Sym2 (Site d)) | m e = 0} =
          {m : InfiniteCurrentConfig (Sym2 (Site d)) |
            m (g⁻¹ • e) = 0} := rfl
      rw [hpre]
      apply hzero
      intro hedge
      apply he
      induction e using Sym2.inductionOn with
      | _ x y =>
          rw [Percolation.smul_sym2_mk] at hedge
          rw [SimpleGraph.mem_edgeSet] at hedge ⊢
          exact (Percolation.hyper_adj_smul g⁻¹ x y).1 hedge
    · exact (measurable_pi_apply e) (MeasurableSet.singleton 0)
  have hparity (S : Finset (Sym2 (Site d)))
      (hS : (↑S : Set (Sym2 (Site d))) ⊆
        (hypercubicLattice d).edgeSet) :
      currentParityMarginalPMF rho S = currentParityMarginalPMF mu S :=
    currentParityMarginalPMF_currentShiftLaw_eq d mu g (havoid g) S hS
  have hlatticeMarginal (S : Finset (Sym2 (Site d)))
      (hS : (↑S : Set (Sym2 (Site d))) ⊆
        (hypercubicLattice d).edgeSet) :
      currentMarginal rho S = currentMarginal mu S := by
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_singleton
    intro a
    rw [currentMarginal_apply, currentMarginal_apply]
    rw [currentShiftLaw_apply]
    · rw [preimage_currentCylinder_singleton_currentShift]
      let Sg := currentShiftFinset g S
      let ag := currentShiftPattern g S a
      have hSg : (↑Sg : Set (Sym2 (Site d))) ⊆
          (hypercubicLattice d).edgeSet :=
        currentShiftFinset_lattice d g S hS
      rw [hfactor Sg hSg ag, hfactor S hS a]
      have hparEvent :
          (mu : Measure _)
              (currentParityPatternCylinder Sg (currentLocalParity ag)) =
            (rho : Measure _)
              (currentParityPatternCylinder S (currentLocalParity a)) := by
        rw [currentShiftLaw_apply]
        · rw [preimage_currentParityPatternCylinder_currentShift,
            currentLocalParity_shiftPattern]
        · have hset : currentParityPatternCylinder S (currentLocalParity a) =
              currentCylinder S
                {b | currentLocalParity b = currentLocalParity a} := rfl
          rw [hset]
          exact measurableSet_currentCylinder _ _
      rw [hparEvent]
      have hp := congrArg
        (fun p : PMF (↑S -> Bool) => p (currentLocalParity a))
        (hparity S hS)
      have hp' :
          (rho : Measure _)
              (currentParityPatternCylinder S (currentLocalParity a)) =
            (mu : Measure _)
              (currentParityPatternCylinder S (currentLocalParity a)) := by
        simpa only [currentParityMarginalPMF_apply] using hp
      rw [hp']
      have hk : finiteParityPMF Sg beta hbeta
            (currentLocalParity ag) ag =
          finiteParityPMF S beta hbeta (currentLocalParity a) a := by
        simpa [Sg, ag, currentLocalParity_shiftPattern] using
          (finiteParityPMF_shiftPattern g S beta hbeta
            (currentLocalParity a) a)
      rw [hk]
    · exact measurableSet_currentCylinder _ _
  have hmarginal : ∀ S : Finset (Sym2 (Site d)),
      currentMarginal rho S = currentMarginal mu S := by
    intro S
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_singleton
    intro a
    rw [currentMarginal_apply, currentMarginal_apply,
      currentCylinder_singleton_reduce_lattice d rho S hrhoZero a,
      currentCylinder_singleton_reduce_lattice d mu S hzero a]
    split_ifs
    · have hL := hlatticeMarginal (latticeEdgePart d S)
        (latticeEdgePart_lattice d S)
      have happ := congrArg (fun p : ProbabilityMeasure
        (↑(latticeEdgePart d S) -> Nat) =>
          (p : Measure (↑(latticeEdgePart d S) -> Nat))
            {Finset.restrict₂ (π := fun _ : Sym2 (Site d) => Nat)
              (latticeEdgePart_subset d S) a}) hL
      simpa only [currentMarginal_apply] using happ
    · rfl
  have hrho : rho = mu := ProbabilityMeasure.ext_of_currentMarginal_eq hmarginal
  refine ⟨measurable_currentShift g, ?_⟩
  exact congrArg ProbabilityMeasure.toMeasure hrho


theorem infinitePlusCurrentMeasure_isTranslationInvariant
    (d : Nat) (beta : Real) (hbeta : 0 < beta) :
    CurrentIsTranslationInvariant (H := Multiplicative (Site d))
      (infinitePlusCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
  apply currentLimit_isTranslationInvariant d beta hbeta
    (infinitePlusCurrentMeasure d beta hbeta.le)
  · intro e he
    exact plusCurrentLimit_nonlattice_zero d beta hbeta.le e he
      (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta.le)
  · intro S hS a
    exact plusCurrentLimit_pattern_factor d beta hbeta S hS
      (infiniteCurrentBoxSubsequence_strictMono d beta hbeta.le)
      (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta.le) a
  · intro g F hF
    rw [preimage_currentParityAvoidCylinder_currentShift,
      infinitePlusCurrentMeasure_parityAvoid_eq d beta hbeta
        (currentShiftFinset g F) (currentShiftFinset_lattice d g F hF),
      infinitePlusCurrentMeasure_parityAvoid_eq d beta hbeta F hF]
    rw [integral_exp_neg_edgeSpinSum_shift d beta
      (plusState d beta 0 : Measure (ConfigSpace (Site d)))
      (iptp_plusState_isTranslationInvariant hbeta.le le_rfl) g F]
    rw [show (currentShiftFinset g F).card = F.card by
      unfold currentShiftFinset
      exact Finset.card_image_of_injective _ (MulAction.injective g⁻¹)]


theorem infiniteFreeCurrentMeasure_isTranslationInvariant
    (d : Nat) (beta : Real) (hbeta : 0 < beta) :
    CurrentIsTranslationInvariant (H := Multiplicative (Site d))
      (infiniteFreeCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
  apply currentLimit_isTranslationInvariant d beta hbeta
    (infiniteFreeCurrentMeasure d beta hbeta.le)
  · intro e he
    exact freeCurrentLimit_nonlattice_zero d beta hbeta.le e he
      (freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta.le)
  · intro S hS a
    exact freeCurrentLimit_pattern_factor d beta hbeta S hS
      (infiniteCurrentBoxSubsequence_strictMono d beta hbeta.le)
      (freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta.le) a
  · intro g F hF
    rw [preimage_currentParityAvoidCylinder_currentShift,
      infiniteFreeCurrentMeasure_parityAvoid_eq d beta hbeta
        (currentShiftFinset g F) (currentShiftFinset_lattice d g F hF),
      infiniteFreeCurrentMeasure_parityAvoid_eq d beta hbeta F hF]
    rw [integral_exp_neg_edgeSpinSum_shift d beta
      (freeState d beta 0 : Measure (ConfigSpace (Site d)))
      (freeState_isTranslationInvariant d beta hbeta.le) g F]
    rw [show (currentShiftFinset g F).card = F.card by
      unfold currentShiftFinset
      exact Finset.card_image_of_injective _ (MulAction.injective g⁻¹)]

end StatMech.FrontierB
