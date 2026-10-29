/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityLimits
import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentPatternFactor.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentMeasures
import Def.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part2
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

theorem preimage_boolAvoid_currentLocalParity_restrictCurrent
    {E : Type*} [DecidableEq E] (S : Finset E) (T : Finset ↑S) :
    (currentLocalParity ∘ restrictCurrent S) ⁻¹' boolAvoid T =
      currentParityAvoidCylinder (ambientSubfinset S T) := by
  ext m
  simp only [Set.mem_preimage, Function.comp_apply, boolAvoid,
    Set.mem_setOf_eq, currentParityAvoidCylinder]
  rw [Finset.disjoint_left]
  constructor
  · intro h e heT
    have heT' : e ∈ T.map ⟨Subtype.val, Subtype.val_injective⟩ := by
      simpa [ambientSubfinset] using heT
    rw [Finset.mem_map] at heT'
    obtain ⟨i, hiT, rfl⟩ := heT'
    by_contra hneven
    have hodd : Odd (m i.1) := Nat.not_even_iff_odd.mp hneven
    apply h (a := i)
    · simp [boolSupport, currentLocalParity, restrictCurrent, hodd]
    · exact hiT
  · intro h i hiSupp hiT
    have heven : Even (m i.1) := h i.1 (by
      simpa [ambientSubfinset] using
        (Finset.mem_map.mpr ⟨i, hiT, rfl⟩ :
          i.1 ∈ T.map ⟨Subtype.val, Subtype.val_injective⟩))
    have hodd : Odd (m i.1) := by
      simpa [boolSupport, currentLocalParity, restrictCurrent] using hiSupp
    exact (Nat.not_even_iff_odd.mpr hodd) heven

theorem currentParityMarginalPMF_avoid
    {E : Type*} [Countable E] [DecidableEq E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (S : Finset E) (T : Finset ↑S) :
    (currentParityMarginalPMF mu S).toMeasure (boolAvoid T) =
      (mu : Measure (InfiniteCurrentConfig E))
        (currentParityAvoidCylinder (ambientSubfinset S T)) := by
  rw [currentParityMarginalPMF_toMeasure]
  change Measure.map currentLocalParity
      (currentMarginal mu S : Measure (↑S → ℕ)) (boolAvoid T) = _
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  change Measure.map (restrictCurrent S)
      (mu : Measure (InfiniteCurrentConfig E))
      (currentLocalParity ⁻¹' boolAvoid T) = _
  rw [Measure.map_apply (continuous_restrictCurrent S).measurable
    MeasurableSet.of_discrete]
  rw [← preimage_boolAvoid_currentLocalParity_restrictCurrent S T]
  rfl

theorem currentParityMarginalPMF_apply
    {E : Type*} [Countable E] [DecidableEq E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (S : Finset E) (odd : ↑S → Bool) :
    currentParityMarginalPMF mu S odd =
      (mu : Measure (InfiniteCurrentConfig E))
        (currentParityPatternCylinder S odd) := by
  rw [← PMF.toMeasure_apply_singleton _ odd (MeasurableSet.singleton odd),
    currentParityMarginalPMF_toMeasure]
  change Measure.map currentLocalParity
      (currentMarginal mu S : Measure (↑S → ℕ)) {odd} = _
  rw [Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton odd)]
  change Measure.map (restrictCurrent S)
      (mu : Measure (InfiniteCurrentConfig E))
      (currentLocalParity ⁻¹' {odd}) = _
  rw [Measure.map_apply (continuous_restrictCurrent S).measurable
    MeasurableSet.of_discrete]
  rfl

theorem WeakCurrentConverges.cylinderENNReal
    {E : Type*} [Countable E]
    {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (h : WeakCurrentConverges mu nu) (S : Finset E)
    (A : Set (↑S → ℕ)) :
    Tendsto (fun k => (mu k : Measure (InfiniteCurrentConfig E))
        (currentCylinder S A)) atTop
      (nhds ((nu : Measure (InfiniteCurrentConfig E))
        (currentCylinder S A))) := by
  have hc := (ENNReal.tendsto_coe).2 (h.cylinder S A)
  simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc

theorem currentParityAvoidCylinder_eq_currentCylinder {E : Type*}
    (S : Finset E) :
    currentParityAvoidCylinder S =
      currentCylinder S {a | ∀ i, Even (a i)} := by
  ext m
  simp [currentParityAvoidCylinder, currentCylinder, restrictCurrent]


theorem currentLimit_parityMarginal_eq_of_avoid_tendsto
    {E : Type*} [Countable E] [DecidableEq E]
    (mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E))
    (havoid : ∀ A : Finset E, ∃ L : ENNReal,
      Tendsto (fun n => (mu n : Measure (InfiniteCurrentConfig E))
        (currentParityAvoidCylinder A)) atTop (nhds L))
    (S : Finset E)
    {nu rho : ProbabilityMeasure (InfiniteCurrentConfig E)}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges (mu ∘ phi) nu)
    (hrho : WeakCurrentConverges (mu ∘ psi) rho) :
    currentParityMarginalPMF nu S = currentParityMarginalPMF rho S := by
  apply PMF.ext_of_boolAvoid_eq
  intro T
  rw [currentParityMarginalPMF_avoid, currentParityMarginalPMF_avoid]
  let A := ambientSubfinset S T
  obtain ⟨L, hfull⟩ := havoid A
  have hsubPhi := hfull.comp hphi.tendsto_atTop
  have hsubPsi := hfull.comp hpsi.tendsto_atTop
  have hportPhi := hnu.cylinder A {a | ∀ i, Even (a i)}
  have hportPsi := hrho.cylinder A {a | ∀ i, Even (a i)}
  rw [← currentParityAvoidCylinder_eq_currentCylinder] at hportPhi hportPsi
  have hportPhi' : Tendsto
      ((fun n => (mu n : Measure (InfiniteCurrentConfig E))
        (currentParityAvoidCylinder A)) ∘ phi) atTop
      (nhds ((nu : Measure _) (currentParityAvoidCylinder A))) := by
    have hc := (ENNReal.tendsto_coe).2 hportPhi
    simpa [Function.comp_def,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc
  have hportPsi' : Tendsto
      ((fun n => (mu n : Measure (InfiniteCurrentConfig E))
        (currentParityAvoidCylinder A)) ∘ psi) atTop
      (nhds ((rho : Measure _) (currentParityAvoidCylinder A))) := by
    have hc := (ENNReal.tendsto_coe).2 hportPsi
    simpa [Function.comp_def,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc
  exact (tendsto_nhds_unique hsubPhi hportPhi').symm.trans
    (tendsto_nhds_unique hsubPsi hportPsi')


theorem currentMarginal_eq_of_parityMarginal_eq_of_pattern_factor
    {E : Type*} [Countable E] [DecidableEq E]
    (mu nu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (S : Finset E) (kernel : (↑S → Bool) → (↑S → ℕ) → ENNReal)
    (hparity : currentParityMarginalPMF mu S =
      currentParityMarginalPMF nu S)
    (hmu : ∀ a : ↑S → ℕ,
      (mu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (mu : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel (currentLocalParity a) a)
    (hnu : ∀ a : ↑S → ℕ,
      (nu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (nu : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel (currentLocalParity a) a) :
    currentMarginal mu S = currentMarginal nu S := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  rw [currentMarginal_apply, currentMarginal_apply, hmu a, hnu a]
  congr 1
  have hp := congrArg
    (fun p : PMF (↑S → Bool) => p (currentLocalParity a)) hparity
  simpa only [currentParityMarginalPMF_apply] using hp


theorem ProbabilityMeasure.ext_of_currentParity_and_pattern_factor
    {E : Type*} [Countable E] [DecidableEq E]
    (mu nu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (kernel : ∀ S : Finset E, (↑S → Bool) → (↑S → ℕ) → ENNReal)
    (hparity : ∀ S, currentParityMarginalPMF mu S =
      currentParityMarginalPMF nu S)
    (hmu : ∀ (S : Finset E) (a : ↑S → ℕ),
      (mu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (mu : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel S (currentLocalParity a) a)
    (hnu : ∀ (S : Finset E) (a : ↑S → ℕ),
      (nu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (nu : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel S (currentLocalParity a) a) :
    mu = nu := by
  apply ProbabilityMeasure.ext_of_currentMarginal_eq
  intro S
  exact currentMarginal_eq_of_parityMarginal_eq_of_pattern_factor
    mu nu S (kernel S) (hparity S) (hmu S) (hnu S)


theorem WeakCurrentConverges.pattern_factor_of_eventually
    {E : Type*} [Countable E] [DecidableEq E]
    {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (hnu : WeakCurrentConverges mu nu)
    (S : Finset E) (kernel : (↑S → Bool) → (↑S → ℕ) → ENNReal)
    (hkernelTop : ∀ odd a, kernel odd a ≠ ⊤)
    (hfactor : ∀ a : ↑S → ℕ, ∀ᶠ n in atTop,
      (mu n : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (mu n : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel (currentLocalParity a) a)
    (a : ↑S → ℕ) :
    (nu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
      (nu : Measure (InfiniteCurrentConfig E))
          (currentParityPatternCylinder S (currentLocalParity a)) *
        kernel (currentLocalParity a) a := by
  have hpoint := hnu.cylinderENNReal S {a}
  have hparity := hnu.cylinderENNReal S
    {b | currentLocalParity b = currentLocalParity a}
  have hproduct := (ENNReal.continuous_mul_const
    (hkernelTop (currentLocalParity a) a)).continuousAt.tendsto.comp hparity
  have hpoint' := hpoint
  have hproduct' := hproduct
  have hproductCurrent := hproduct'.congr' (by
    filter_upwards [hfactor a] with n hn
    exact hn.symm)
  exact tendsto_nhds_unique hpoint' hproductCurrent


theorem currentLimit_eq_of_avoid_tendsto_of_pattern_factor
    {E : Type*} [Countable E] [DecidableEq E]
    (mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E))
    (havoid : ∀ A : Finset E, ∃ L : ENNReal,
      Tendsto (fun n => (mu n : Measure (InfiniteCurrentConfig E))
        (currentParityAvoidCylinder A)) atTop (nhds L))
    (kernel : ∀ S : Finset E,
      (↑S → Bool) → (↑S → ℕ) → ENNReal)
    {nu rho : ProbabilityMeasure (InfiniteCurrentConfig E)}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges (mu ∘ phi) nu)
    (hrho : WeakCurrentConverges (mu ∘ psi) rho)
    (hnuFactor : ∀ (S : Finset E) (a : ↑S → ℕ),
      (nu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (nu : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel S (currentLocalParity a) a)
    (hrhoFactor : ∀ (S : Finset E) (a : ↑S → ℕ),
      (rho : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (rho : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel S (currentLocalParity a) a) :
    nu = rho := by
  apply ProbabilityMeasure.ext_of_currentParity_and_pattern_factor
    nu rho kernel
  · intro S
    exact currentLimit_parityMarginal_eq_of_avoid_tendsto
      mu havoid S hphi hpsi hnu hrho
  · exact hnuFactor
  · exact hrhoFactor

theorem ambientSubfinset_lattice
    (d : ℕ) (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (T : Finset ↑S) :
    (↑(ambientSubfinset S T) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
  intro e he
  have he' : e ∈ T.map ⟨Subtype.val, Subtype.val_injective⟩ := by
    simpa [ambientSubfinset] using he
  rw [Finset.mem_map] at he'
  obtain ⟨i, hi, rfl⟩ := he'
  exact hS i.2

theorem plusCurrentLimit_parityMarginal_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ psi) rho) :
    currentParityMarginalPMF nu S = currentParityMarginalPMF rho S := by
  apply PMF.ext_of_boolAvoid_eq
  intro T
  rw [currentParityMarginalPMF_avoid, currentParityMarginalPMF_avoid]
  let A := ambientSubfinset S T
  have hA : (↑A : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet :=
    ambientSubfinset_lattice d S hS T
  have hfull := plusBoxCurrentMeasure_parityAvoid_full_tendsto
    d beta hbeta A hA
  have hsubPhi := hfull.comp hphi.tendsto_atTop
  have hsubPsi := hfull.comp hpsi.tendsto_atTop
  have hportPhi := hnu.cylinder A {a | ∀ i, Even (a i)}
  have hportPsi := hrho.cylinder A {a | ∀ i, Even (a i)}
  rw [← currentParityAvoidCylinder_eq_currentCylinder] at hportPhi hportPsi
  have hportPhi' : Tendsto
      ((fun n => (plusBoxCurrentMeasure d n beta hbeta : Measure _)
        (currentParityAvoidCylinder A)) ∘ phi) atTop
      (nhds ((nu : Measure _) (currentParityAvoidCylinder A))) := by
    have hc := (ENNReal.tendsto_coe).2 hportPhi
    simpa [Function.comp_def,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc
  have hportPsi' : Tendsto
      ((fun n => (plusBoxCurrentMeasure d n beta hbeta : Measure _)
        (currentParityAvoidCylinder A)) ∘ psi) atTop
      (nhds ((rho : Measure _) (currentParityAvoidCylinder A))) := by
    have hc := (ENNReal.tendsto_coe).2 hportPsi
    simpa [Function.comp_def,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc
  simpa [A] using (tendsto_nhds_unique hsubPhi hportPhi').symm.trans
    (tendsto_nhds_unique hsubPsi hportPsi')

theorem freeCurrentLimit_parityMarginal_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ psi) rho) :
    currentParityMarginalPMF nu S = currentParityMarginalPMF rho S := by
  apply PMF.ext_of_boolAvoid_eq
  intro T
  rw [currentParityMarginalPMF_avoid, currentParityMarginalPMF_avoid]
  let A := ambientSubfinset S T
  have hA : (↑A : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet :=
    ambientSubfinset_lattice d S hS T
  have hfull := freeBoxCurrentMeasure_parityAvoid_full_tendsto
    d beta hbeta A hA
  have hsubPhi := hfull.comp hphi.tendsto_atTop
  have hsubPsi := hfull.comp hpsi.tendsto_atTop
  have hportPhi := hnu.cylinder A {a | ∀ i, Even (a i)}
  have hportPsi := hrho.cylinder A {a | ∀ i, Even (a i)}
  rw [← currentParityAvoidCylinder_eq_currentCylinder] at hportPhi hportPsi
  have hportPhi' : Tendsto
      ((fun n => (freeBoxCurrentMeasure d n beta hbeta : Measure _)
        (currentParityAvoidCylinder A)) ∘ phi) atTop
      (nhds ((nu : Measure _) (currentParityAvoidCylinder A))) := by
    have hc := (ENNReal.tendsto_coe).2 hportPhi
    simpa [Function.comp_def,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc
  have hportPsi' : Tendsto
      ((fun n => (freeBoxCurrentMeasure d n beta hbeta : Measure _)
        (currentParityAvoidCylinder A)) ∘ psi) atTop
      (nhds ((rho : Measure _) (currentParityAvoidCylinder A))) := by
    have hc := (ENNReal.tendsto_coe).2 hportPsi
    simpa [Function.comp_def,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc
  simpa [A] using (tendsto_nhds_unique hsubPhi hportPhi').symm.trans
    (tendsto_nhds_unique hsubPsi hportPsi')

theorem plusCurrentLimit_pattern_factor
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (a : ↑S → ℕ) :
    (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder S {a}) =
      (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityPatternCylinder S (currentLocalParity a)) *
        finiteParityPMF S beta hbeta (currentLocalParity a) a := by
  obtain ⟨N, hSN⟩ := finiteLatticeEdges_subset_bondFinsetTouch d S hS
  have hpoint := hnu.cylinderENNReal S {a}
  have hparity := hnu.cylinderENNReal S
    {b | currentLocalParity b = currentLocalParity a}
  have hprod := (ENNReal.continuous_mul_const
    (PMF.apply_ne_top
      (finiteParityPMF S beta hbeta (currentLocalParity a)) a)).continuousAt.tendsto.comp
        hparity
  have hev : ∀ᶠ k in atTop,
      (plusBoxCurrentMeasure d (phi k) beta hbeta.le : Measure _)
          (currentCylinder S {a}) =
        (plusBoxCurrentMeasure d (phi k) beta hbeta.le : Measure _)
            (currentParityPatternCylinder S (currentLocalParity a)) *
          finiteParityPMF S beta hbeta (currentLocalParity a) a := by
    filter_upwards [eventually_ge_atTop (N + 1)] with k hk
    have hindex : N + 1 ≤ phi k := hk.trans (hphi.id_le k)
    let n := phi k - 1
    have hphi_eq : phi k = n + 1 := by omega
    rw [hphi_eq]
    apply plusBoxCurrentMeasure_pattern_factor d n beta hbeta S
      (hSN.trans (StatMech.Ising.bondFinsetTouch_subset (by omega))) a
  have hpoint' := hpoint
  have hprod' := hprod
  simp only [Function.comp_apply] at hpoint' hprod'
  have hprodCurrent := hprod'.congr' (by
    filter_upwards [hev] with k hk
    exact hk.symm)
  exact tendsto_nhds_unique hpoint' hprodCurrent

theorem freeCurrentLimit_pattern_factor
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (a : ↑S → ℕ) :
    (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder S {a}) =
      (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityPatternCylinder S (currentLocalParity a)) *
        finiteParityPMF S beta hbeta (currentLocalParity a) a := by
  obtain ⟨N, hSN⟩ := finiteLatticeEdges_subset_bondFinsetTouch d S hS
  have hpoint := hnu.cylinderENNReal S {a}
  have hparity := hnu.cylinderENNReal S
    {b | currentLocalParity b = currentLocalParity a}
  have hprod := (ENNReal.continuous_mul_const
    (PMF.apply_ne_top
      (finiteParityPMF S beta hbeta (currentLocalParity a)) a)).continuousAt.tendsto.comp
        hparity
  have hev : ∀ᶠ k in atTop,
      (freeBoxCurrentMeasure d (phi k) beta hbeta.le : Measure _)
          (currentCylinder S {a}) =
        (freeBoxCurrentMeasure d (phi k) beta hbeta.le : Measure _)
            (currentParityPatternCylinder S (currentLocalParity a)) *
          finiteParityPMF S beta hbeta (currentLocalParity a) a := by
    filter_upwards [eventually_ge_atTop (N + 1)] with k hk
    have hindex : N + 1 ≤ phi k := hk.trans (hphi.id_le k)
    let n := phi k - 1
    have hphi_eq : phi k = n + 1 := by omega
    rw [hphi_eq]
    apply freeBoxCurrentMeasure_pattern_factor d n beta hbeta S
      (hSN.trans (StatMech.Ising.bondFinsetTouch_subset (by omega))) a
  have hpoint' := hpoint
  have hprod' := hprod
  simp only [Function.comp_apply] at hpoint' hprod'
  have hprodCurrent := hprod'.congr' (by
    filter_upwards [hev] with k hk
    exact hk.symm)
  exact tendsto_nhds_unique hpoint' hprodCurrent

theorem plusCurrentLimit_latticeMarginal_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
    currentMarginal nu S = currentMarginal rho S := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  rw [currentMarginal_apply, currentMarginal_apply]
  rw [plusCurrentLimit_pattern_factor d beta hbeta S hS hphi hnu a,
    plusCurrentLimit_pattern_factor d beta hbeta S hS hpsi hrho a]
  congr 1
  have hp := congrArg (fun p : PMF (↑S → Bool) => p (currentLocalParity a))
    (plusCurrentLimit_parityMarginal_eq d beta hbeta.le S hS
      hphi hpsi hnu hrho)
  simpa only [currentParityMarginalPMF_apply] using hp

theorem freeCurrentLimit_latticeMarginal_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
    currentMarginal nu S = currentMarginal rho S := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  rw [currentMarginal_apply, currentMarginal_apply]
  rw [freeCurrentLimit_pattern_factor d beta hbeta S hS hphi hnu a,
    freeCurrentLimit_pattern_factor d beta hbeta S hS hpsi hrho a]
  congr 1
  have hp := congrArg (fun p : PMF (↑S → Bool) => p (currentLocalParity a))
    (freeCurrentLimit_parityMarginal_eq d beta hbeta.le S hS
      hphi hpsi hnu hrho)
  simpa only [currentParityMarginalPMF_apply] using hp

theorem boxCurrentEdgeIncl_mem_lattice
    (d n : ℕ) (e : (StatMech.FK.boxGraph d n).edgeFinset) :
    boxCurrentEdgeIncl d n e ∈ (hypercubicLattice d).edgeSet := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at he
      change (hypercubicLattice d).Adj x.1 y.1
      exact he

theorem boxCurrentEdgeIncl_ne_nonlattice
    (d n : ℕ) (e : Sym2 (Site d))
    (he : e ∉ (hypercubicLattice d).edgeSet) :
    e ∉ Set.range (boxCurrentEdgeIncl d n) := by
  rintro ⟨f, rfl⟩
  exact he (boxCurrentEdgeIncl_mem_lattice d n f)

theorem freeBoxCurrentMeasure_nonlattice_zero
    (d n : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Sym2 (Site d)) (he : e ∉ (hypercubicLattice d).edgeSet) :
    (freeBoxCurrentMeasure d n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
      {m | m e = 0} = 1 := by
  have hmeas : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) | m e = 0} :=
    (measurable_pi_apply e) (MeasurableSet.singleton 0)
  change Measure.map (extendBoxCurrent d n)
    (sourcelessCurrentPMF (StatMech.FK.boxGraph d n) beta
      (fun _ => 1) hbeta (fun _ => zero_le_one)).toMeasure
      {m | m e = 0} = 1
  rw [Measure.map_apply (measurable_extendBoxCurrent d n) hmeas]
  have hout := boxCurrentEdgeIncl_ne_nonlattice d n e he
  have hpre : extendBoxCurrent d n ⁻¹' {m | m e = 0} = Set.univ := by
    ext m
    simp [extendBoxCurrent_outside d n m e hout]
  rw [hpre, measure_univ]

theorem plusBoxCurrentMeasure_nonlattice_zero
    (d n : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Sym2 (Site d)) (he : e ∉ (hypercubicLattice d).edgeSet) :
    (plusBoxCurrentMeasure d n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
      {m | m e = 0} = 1 := by
  have hmeas : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) | m e = 0} :=
    (measurable_pi_apply e) (MeasurableSet.singleton 0)
  change Measure.map (extendBoxCurrent d n)
    (boundaryCurrentPMF (StatMech.FK.boxGraph d n) beta (fun _ => 1)
      hbeta (fun _ => zero_le_one) (boxCurrentInterior d n)).toMeasure
      {m | m e = 0} = 1
  rw [Measure.map_apply (measurable_extendBoxCurrent d n) hmeas]
  have hout := boxCurrentEdgeIncl_ne_nonlattice d n e he
  have hpre : extendBoxCurrent d n ⁻¹' {m | m e = 0} = Set.univ := by
    ext m
    simp [extendBoxCurrent_outside d n m e hout]
  rw [hpre, measure_univ]

theorem plusCurrentLimit_nonlattice_zero
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Sym2 (Site d)) (he : e ∉ (hypercubicLattice d).edgeSet)
    {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : ℕ → ℕ}
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ phi) nu) :
    (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
      {m | m e = 0} = 1 := by
  let S : Finset (Sym2 (Site d)) := {e}
  let A : Set (↑S → ℕ) := {a | a ⟨e, by simp [S]⟩ = 0}
  have hset : currentCylinder S A = {m | m e = 0} := by
    ext m
    simp [currentCylinder, restrictCurrent, A, S]
  have hlim := hnu.cylinderENNReal S A
  rw [hset] at hlim
  have hone : Tendsto
      (fun k => (plusBoxCurrentMeasure d (phi k) beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0}) atTop (nhds 1) := by
    simpa only [plusBoxCurrentMeasure_nonlattice_zero d _ beta hbeta e he]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ENNReal)) atTop (nhds 1))
  exact tendsto_nhds_unique hlim hone

theorem freeCurrentLimit_nonlattice_zero
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Sym2 (Site d)) (he : e ∉ (hypercubicLattice d).edgeSet)
    {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : ℕ → ℕ}
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nu) :
    (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
      {m | m e = 0} = 1 := by
  let S : Finset (Sym2 (Site d)) := {e}
  let A : Set (↑S → ℕ) := {a | a ⟨e, by simp [S]⟩ = 0}
  have hset : currentCylinder S A = {m | m e = 0} := by
    ext m
    simp [currentCylinder, restrictCurrent, A, S]
  have hlim := hnu.cylinderENNReal S A
  rw [hset] at hlim
  have hone : Tendsto
      (fun k => (freeBoxCurrentMeasure d (phi k) beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0}) atTop (nhds 1) := by
    simpa only [freeBoxCurrentMeasure_nonlattice_zero d _ beta hbeta e he]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ENNReal)) atTop (nhds 1))
  exact tendsto_nhds_unique hlim hone

end StatMech.FrontierB
