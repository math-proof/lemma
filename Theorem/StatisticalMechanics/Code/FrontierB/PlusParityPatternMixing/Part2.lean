/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.PlusEvenMixing.Part2
import Def.StatisticalMechanics.Code.FrontierB.PlusParityPatternMixing.Part3
open MeasureTheory Set
open scoped BigOperators


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.ConfigSpace StatMech.FK

theorem plusParityPatternSpinPolynomial_eq_multiOpenExpansion {d : Nat}
    (beta : Real) (S : Finset (Sym2 (Site d))) (odd : ↑S -> Bool)
    (hS : ∀ e ∈ S, ¬ e.IsDiag) (omega : ConfigSpace (Site d)) :
    plusParityPatternSpinPolynomial beta S odd omega =
      ∑ i ∈ plusParityExpansionIndices S,
        plusParityExpansionCoeff beta S odd i *
          fmu_moInd (plusParityExpansionSupport i) omega := by
  unfold plusParityPatternSpinPolynomial
  rw [plusParityExpansionIndices, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro T hT
  have hTdiag : ∀ e ∈ T, ¬ e.IsDiag := by
    intro e he
    exact hS e (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he)
  rw [exp_neg_edgeSpinSum_eq_plusEvenExpansion beta T hTdiag omega]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [plusParityExpansionCoeff, plusParityExpansionSupport,
    plusEvenExpansionSupport]
  ring

theorem integral_plusParityPatternSpinPolynomial_eq_multiOpenExpansion
    {d : Nat} (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (beta : Real) (S : Finset (Sym2 (Site d))) (odd : ↑S -> Bool)
    (hS : ∀ e ∈ S, ¬ e.IsDiag) :
    (∫ omega, plusParityPatternSpinPolynomial beta S odd omega ∂mu) =
      ∑ i ∈ plusParityExpansionIndices S,
        plusParityExpansionCoeff beta S odd i *
          mu.real (fmu_multiOpen (plusParityExpansionSupport i)) := by
  have hfun : (fun omega => plusParityPatternSpinPolynomial beta S odd omega) =
      fun omega => ∑ i ∈ plusParityExpansionIndices S,
        plusParityExpansionCoeff beta S odd i *
          fmu_moInd (plusParityExpansionSupport i) omega := by
    funext omega
    exact plusParityPatternSpinPolynomial_eq_multiOpenExpansion
      beta S odd hS omega
  rw [hfun, MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [MeasureTheory.integral_const_mul, fmu_integral_moInd]
  · intro i hi
    exact (fmu_integrable_moInd (plusParityExpansionSupport i)).const_mul _

theorem infinitePlusCurrentMeasure_parityPattern_real_eq_integral {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d))) (odd : ↑S -> Bool)
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityPatternCylinder S odd) =
      ∫ omega, plusParityPatternSpinPolynomial beta S odd omega
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
  rw [infinitePlusCurrentMeasure_parityPattern_real_eq hbeta S odd hS]
  unfold plusParityPatternSpinPolynomial
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T hT
    rw [MeasureTheory.integral_const_mul]
    ring
  · intro T hT
    apply Integrable.const_mul
    have hTdiag : ∀ e ∈ T, ¬ e.IsDiag := by
      intro e he
      exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet
        (hS (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he))
    have hexp : (fun omega : ConfigSpace (Site d) =>
        Real.exp (-beta * edgeSpinSum T omega)) =
        fun omega => ∑ i ∈ plusEvenExpansionIndices T,
          plusEvenExpansionCoeff beta T i *
            fmu_moInd (plusEvenExpansionSupport i) omega := by
      funext omega
      exact exp_neg_edgeSpinSum_eq_plusEvenExpansion beta T hTdiag omega
    rw [hexp]
    apply MeasureTheory.integrable_finsetSum
    intro i hi
    exact (fmu_integrable_moInd (plusEvenExpansionSupport i)).const_mul _

theorem currentParityPattern_inter_shift_real_eq_avoid_sum
    {E H : Type*} [Countable E] [DecidableEq E] [Group H] [MulAction H E]
    (mu : Measure (InfiniteCurrentConfig E)) [IsProbabilityMeasure mu]
    (g : H) (S S' : Finset E) (odd : ↑S -> Bool) (odd' : ↑S' -> Bool) :
    mu.real (currentParityPatternCylinder S odd ∩
        (currentShift g) ⁻¹' currentParityPatternCylinder S' odd') =
      ∑ T ∈ S.powerset, ∑ U ∈ S'.powerset,
        currentParityTraceCoeff S odd T * currentParityTraceCoeff S' odd' U *
          mu.real (currentParityAvoidCylinder T ∩
            (currentShift g) ⁻¹' currentParityAvoidCylinder U) := by
  let A := currentParityPatternCylinder S odd
  let B := currentParityPatternCylinder S' odd'
  have hA : MeasurableSet A := measurableSet_currentCylinder S _
  have hB : MeasurableSet B := measurableSet_currentCylinder S' _
  have hAB : MeasurableSet (A ∩ (currentShift g) ⁻¹' B) :=
    hA.inter (hB.preimage (measurable_currentShift g))
  rw [show mu.real (A ∩ (currentShift g) ⁻¹' B) =
      ∫ m, A.indicator (fun _ => (1 : Real)) m *
        B.indicator (fun _ => (1 : Real)) (currentShift g m) ∂mu by
    rw [show mu.real (A ∩ (currentShift g) ⁻¹' B) =
        ∫ m, (A ∩ (currentShift g) ⁻¹' B).indicator
          (fun _ => (1 : Real)) m ∂mu by
      rw [MeasureTheory.integral_indicator_const (1 : Real) hAB]
      simp]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with m
    have hcomp : B.indicator (fun _ => (1 : Real)) (currentShift g m) =
        ((currentShift g) ⁻¹' B).indicator (fun _ => (1 : Real)) m :=
      (Set.indicator_comp_right (s := B) (f := currentShift g)
        (g := fun _ => (1 : Real)) (x := m)).symm
    rw [hcomp]
    simpa only [one_mul] using
      (Set.inter_indicator_mul (s := A) (t := (currentShift g) ⁻¹' B)
        (fun _ => (1 : Real)) (fun _ => (1 : Real)) m)]
  dsimp [A, B]
  simp_rw [currentParityPattern_indicator_eq_avoid_sum S odd,
    currentParityPattern_indicator_eq_avoid_sum S' odd']
  have hpoint (m : InfiniteCurrentConfig E) :
      (∑ T ∈ S.powerset, currentParityTraceCoeff S odd T *
          (currentParityAvoidCylinder T).indicator (fun _ => (1 : Real)) m) *
        (∑ U ∈ S'.powerset, currentParityTraceCoeff S' odd' U *
          (currentParityAvoidCylinder U).indicator (fun _ => (1 : Real))
            (currentShift g m)) =
      ∑ T ∈ S.powerset, ∑ U ∈ S'.powerset,
        (currentParityTraceCoeff S odd T * currentParityTraceCoeff S' odd' U) *
          ((currentParityAvoidCylinder T).indicator (fun _ => (1 : Real)) m *
            (currentParityAvoidCylinder U).indicator (fun _ => (1 : Real))
              (currentShift g m)) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    apply Finset.sum_congr rfl
    intro U hU
    ring
  have hAvoidMeas (T : Finset E) :
      MeasurableSet (currentParityAvoidCylinder T) := by
    rw [currentParityAvoidCylinder_eq_currentCylinder]
    exact measurableSet_currentCylinder T _
  have hprod (T U : Finset E) : (fun m =>
      (currentParityAvoidCylinder T).indicator (fun _ => (1 : Real)) m *
        (currentParityAvoidCylinder U).indicator (fun _ => (1 : Real))
          (currentShift g m)) =
      (currentParityAvoidCylinder T ∩
        (currentShift g) ⁻¹' currentParityAvoidCylinder U).indicator
          (fun _ => (1 : Real)) := by
    funext m
    rw [show (currentParityAvoidCylinder U).indicator
        (fun _ => (1 : Real)) (currentShift g m) =
        ((currentShift g) ⁻¹' currentParityAvoidCylinder U).indicator
          (fun _ => (1 : Real)) m from
      (Set.indicator_comp_right (s := currentParityAvoidCylinder U)
        (f := currentShift g) (g := fun _ => (1 : Real)) (x := m)).symm]
    symm
    simpa only [one_mul] using
      (Set.inter_indicator_mul
        (s := currentParityAvoidCylinder T)
        (t := (currentShift g) ⁻¹' currentParityAvoidCylinder U)
        (fun _ => (1 : Real)) (fun _ => (1 : Real)) m)
  have hprodMeas (T U : Finset E) : MeasurableSet
      (currentParityAvoidCylinder T ∩
        (currentShift g) ⁻¹' currentParityAvoidCylinder U) :=
    (hAvoidMeas T).inter ((hAvoidMeas U).preimage (measurable_currentShift g))
  simp_rw [hpoint]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T hT
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro U hU
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [hprod T U, MeasureTheory.integral_indicator_const (1 : Real)
        (hprodMeas T U)]
      simp
    · intro U hU
      apply Integrable.const_mul
      rw [hprod T U]
      exact (integrable_const (1 : Real)).indicator (hprodMeas T U)
  · intro T hT
    apply MeasureTheory.integrable_finsetSum
    intro U hU
    apply Integrable.const_mul
    rw [hprod T U]
    exact (integrable_const (1 : Real)).indicator (hprodMeas T U)

theorem integrable_exp_neg_edgeSpinSum_mul_shift {d : Nat}
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (beta : Real) (g : Multiplicative (Site d))
    (F F' : Finset (Sym2 (Site d)))
    (hF : ∀ e ∈ F, ¬ e.IsDiag) (hF' : ∀ e ∈ F', ¬ e.IsDiag) :
    Integrable (fun omega => Real.exp (-beta * edgeSpinSum F omega) *
      Real.exp (-beta * edgeSpinSum F' (shift g omega))) mu := by
  have hfun : (fun omega : ConfigSpace (Site d) =>
      Real.exp (-beta * edgeSpinSum F omega) *
        Real.exp (-beta * edgeSpinSum F' (shift g omega))) =
      fun omega => ∑ i ∈ plusEvenExpansionIndices F,
        ∑ j ∈ plusEvenExpansionIndices F',
          (plusEvenExpansionCoeff beta F i *
            plusEvenExpansionCoeff beta F' j) *
          (fmu_moInd (plusEvenExpansionSupport i) omega *
            fmu_moInd (plusEvenExpansionSupport j) (shift g omega)) := by
    funext omega
    rw [exp_neg_edgeSpinSum_eq_plusEvenExpansion beta F hF omega,
      exp_neg_edgeSpinSum_eq_plusEvenExpansion beta F' hF' (shift g omega),
      Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfun]
  apply MeasureTheory.integrable_finsetSum
  intro i hi
  apply MeasureTheory.integrable_finsetSum
  intro j hj
  exact (fmu_integrable_moInd_mul_shift g
    (plusEvenExpansionSupport i) (plusEvenExpansionSupport j)).const_mul _


theorem infinitePlusCurrentMeasure_parityPattern_inter_shift_real_eq_integral
    {d : Nat} {beta : Real} (hbeta : 0 < beta)
    (g : Multiplicative (Site d))
    (S S' : Finset (Sym2 (Site d))) (odd : ↑S -> Bool) (odd' : ↑S' -> Bool)
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hS' : (↑S' : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hdisj : Disjoint S (currentShiftFinset g S')) :
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityPatternCylinder S odd ∩
          (currentShift g) ⁻¹' currentParityPatternCylinder S' odd') =
      ∫ omega, plusParityPatternSpinPolynomial beta S odd omega *
        plusParityPatternSpinPolynomial beta S' odd' (shift g omega)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
  rw [currentParityPattern_inter_shift_real_eq_avoid_sum]
  have hTdiag (T : Finset (Sym2 (Site d))) (hT : T ∈ S.powerset) :
      ∀ e ∈ T, ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet
      (hS (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he))
  have hUdiag (U : Finset (Sym2 (Site d))) (hU : U ∈ S'.powerset) :
      ∀ e ∈ U, ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet
      (hS' (Finset.mem_of_subset (Finset.mem_powerset.mp hU) he))
  have hjoint (T : Finset (Sym2 (Site d))) (hT : T ∈ S.powerset)
      (U : Finset (Sym2 (Site d))) (hU : U ∈ S'.powerset) :
      (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
          (currentParityAvoidCylinder T ∩
            (currentShift g) ⁻¹' currentParityAvoidCylinder U) =
        (∫ omega, Real.exp (-beta * edgeSpinSum T omega) *
            Real.exp (-beta * edgeSpinSum U (shift g omega))
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
          (Real.cosh beta ^ T.card * Real.cosh beta ^ U.card) := by
    apply infinitePlusCurrentMeasure_parityAvoid_inter_shift_real_eq
      hbeta g T U
    · intro e he
      exact hS (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he)
    · intro e he
      exact hS' (Finset.mem_of_subset (Finset.mem_powerset.mp hU) he)
    · apply hdisj.mono (Finset.mem_powerset.mp hT)
      unfold currentShiftFinset
      exact (Finset.image_mono (fun e => g⁻¹ • e))
        (Finset.mem_powerset.mp hU)
  rw [show (∑ T ∈ S.powerset, ∑ U ∈ S'.powerset,
      currentParityTraceCoeff S odd T * currentParityTraceCoeff S' odd' U *
        (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
          (currentParityAvoidCylinder T ∩
            (currentShift g) ⁻¹' currentParityAvoidCylinder U)) =
      ∑ T ∈ S.powerset, ∑ U ∈ S'.powerset,
      currentParityTraceCoeff S odd T * currentParityTraceCoeff S' odd' U *
        ((∫ omega, Real.exp (-beta * edgeSpinSum T omega) *
            Real.exp (-beta * edgeSpinSum U (shift g omega))
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
          (Real.cosh beta ^ T.card * Real.cosh beta ^ U.card)) by
    apply Finset.sum_congr rfl
    intro T hT
    apply Finset.sum_congr rfl
    intro U hU
    rw [hjoint T hT U hU]]
  symm
  unfold plusParityPatternSpinPolynomial
  have hpoint (omega : ConfigSpace (Site d)) :
      (∑ T ∈ S.powerset, currentParityTraceCoeff S odd T *
          Real.cosh beta ^ T.card * Real.exp (-beta * edgeSpinSum T omega)) *
        (∑ U ∈ S'.powerset, currentParityTraceCoeff S' odd' U *
          Real.cosh beta ^ U.card *
            Real.exp (-beta * edgeSpinSum U (shift g omega))) =
      ∑ T ∈ S.powerset, ∑ U ∈ S'.powerset,
        (currentParityTraceCoeff S odd T * currentParityTraceCoeff S' odd' U) *
          ((Real.exp (-beta * edgeSpinSum T omega) *
              Real.exp (-beta * edgeSpinSum U (shift g omega))) *
            (Real.cosh beta ^ T.card * Real.cosh beta ^ U.card)) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    apply Finset.sum_congr rfl
    intro U hU
    ring
  simp_rw [hpoint]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T hT
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro U hU
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_mul_const]
    · intro U hU
      apply Integrable.const_mul
      apply Integrable.mul_const
      exact integrable_exp_neg_edgeSpinSum_mul_shift
        (plusState d beta 0 : Measure (ConfigSpace (Site d))) beta g T U
          (hTdiag T hT) (hUdiag U hU)
  · intro T hT
    apply MeasureTheory.integrable_finsetSum
    intro U hU
    apply Integrable.const_mul
    apply Integrable.mul_const
    exact integrable_exp_neg_edgeSpinSum_mul_shift
      (plusState d beta 0 : Measure (ConfigSpace (Site d))) beta g T U
        (hTdiag T hT) (hUdiag U hU)


theorem infinitePlusCurrentMeasure_parityPattern_pairMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (S S' : Finset (Sym2 (Site d))) (odd : ↑S -> Bool) (odd' : ↑S' -> Bool)
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hS' : (↑S' : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : Multiplicative (Site d),
      Disjoint S (currentShiftFinset g S') ∧
      abs ((infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
          (currentParityPatternCylinder S odd ∩
            (currentShift g) ⁻¹' currentParityPatternCylinder S' odd') -
        (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
            (currentParityPatternCylinder S odd) *
          (infinitePlusCurrentMeasure d beta hbeta.le : Measure _).real
            (currentParityPatternCylinder S' odd')) < epsilon := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let IS := plusParityExpansionIndices S
  let IS' := plusParityExpansionIndices S'
  let sentinel : PlusParityExpansionIndex d :=
    ⟨∅, ⟨∅, edgeVertexSupport S⟩⟩
  let sentinel' : PlusParityExpansionIndex d :=
    ⟨∅, ⟨∅, edgeVertexSupport S'⟩⟩
  let indices := insert sentinel (insert sentinel' (IS ∪ IS'))
  let c := fun i => if i ∈ IS then plusParityExpansionCoeff beta S odd i else 0
  let c' := fun i => if i ∈ IS' then plusParityExpansionCoeff beta S' odd' i else 0
  let mu := (plusState d beta 0 : Measure (ConfigSpace (Site d)))
  have hti : IsTranslationInvariant (G := Multiplicative (Site d)) mu :=
    iptp_plusState_isTranslationInvariant hbeta.le le_rfl
  have hpair : fmu_PairMixing (G := Multiplicative (Site d)) mu :=
    ipe_plusState_pairMixing_of_upperDecay hbeta.le 0 hti
      (icb_plusState_upperDecay hd hbeta.le le_rfl hti)
  obtain ⟨g, hdisj, hcorr⟩ := fmu_finsetExpansion_pairMixing
    (fun x y => siteTranslation_solution_finite x y) hti hpair indices
      plusParityExpansionSupport c c' epsilon hepsilon
  have hIS : IS ⊆ indices := by
    intro i hi
    simp [indices, hi]
  have hIS' : IS' ⊆ indices := by
    intro i hi
    simp [indices, hi]
  have hSdiag : ∀ e ∈ S, ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet (hS he)
  have hS'diag : ∀ e ∈ S', ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet (hS' he)
  have hleftPoint (omega : ConfigSpace (Site d)) :
      (∑ i ∈ indices, c i * fmu_moInd (plusParityExpansionSupport i) omega) =
        plusParityPatternSpinPolynomial beta S odd omega := by
    calc
      (∑ i ∈ indices, c i * fmu_moInd (plusParityExpansionSupport i) omega) =
          ∑ i ∈ IS, c i * fmu_moInd (plusParityExpansionSupport i) omega := by
            refine (Finset.sum_subset hIS (fun i hiIndices hiIS => ?_)).symm
            simp [c, hiIS]
      _ = ∑ i ∈ plusParityExpansionIndices S,
          plusParityExpansionCoeff beta S odd i *
            fmu_moInd (plusParityExpansionSupport i) omega := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [c, IS, hi]
      _ = plusParityPatternSpinPolynomial beta S odd omega :=
        (plusParityPatternSpinPolynomial_eq_multiOpenExpansion
          beta S odd hSdiag omega).symm
  have hrightPoint (omega : ConfigSpace (Site d)) :
      (∑ i ∈ indices, c' i * fmu_moInd (plusParityExpansionSupport i) omega) =
        plusParityPatternSpinPolynomial beta S' odd' omega := by
    calc
      (∑ i ∈ indices, c' i * fmu_moInd (plusParityExpansionSupport i) omega) =
          ∑ i ∈ IS', c' i * fmu_moInd (plusParityExpansionSupport i) omega := by
            refine (Finset.sum_subset hIS' (fun i hiIndices hiIS' => ?_)).symm
            simp [c', hiIS']
      _ = ∑ i ∈ plusParityExpansionIndices S',
          plusParityExpansionCoeff beta S' odd' i *
            fmu_moInd (plusParityExpansionSupport i) omega := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [c', IS', hi]
      _ = plusParityPatternSpinPolynomial beta S' odd' omega :=
        (plusParityPatternSpinPolynomial_eq_multiOpenExpansion
          beta S' odd' hS'diag omega).symm
  have hleftMass :
      (∑ i ∈ indices, c i * mu.real (fmu_multiOpen (plusParityExpansionSupport i))) =
        ∫ omega, plusParityPatternSpinPolynomial beta S odd omega ∂mu := by
    calc
      (∑ i ∈ indices, c i * mu.real (fmu_multiOpen (plusParityExpansionSupport i))) =
          ∑ i ∈ IS, c i * mu.real (fmu_multiOpen (plusParityExpansionSupport i)) := by
            refine (Finset.sum_subset hIS (fun i hiIndices hiIS => ?_)).symm
            simp [c, hiIS]
      _ = ∑ i ∈ plusParityExpansionIndices S,
          plusParityExpansionCoeff beta S odd i *
            mu.real (fmu_multiOpen (plusParityExpansionSupport i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [c, IS, hi]
      _ = ∫ omega, plusParityPatternSpinPolynomial beta S odd omega ∂mu :=
        (integral_plusParityPatternSpinPolynomial_eq_multiOpenExpansion
          mu beta S odd hSdiag).symm
  have hrightMass :
      (∑ i ∈ indices, c' i * mu.real (fmu_multiOpen (plusParityExpansionSupport i))) =
        ∫ omega, plusParityPatternSpinPolynomial beta S' odd' omega ∂mu := by
    calc
      (∑ i ∈ indices, c' i * mu.real (fmu_multiOpen (plusParityExpansionSupport i))) =
          ∑ i ∈ IS', c' i * mu.real (fmu_multiOpen (plusParityExpansionSupport i)) := by
            refine (Finset.sum_subset hIS' (fun i hiIndices hiIS' => ?_)).symm
            simp [c', hiIS']
      _ = ∑ i ∈ plusParityExpansionIndices S',
          plusParityExpansionCoeff beta S' odd' i *
            mu.real (fmu_multiOpen (plusParityExpansionSupport i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [c', IS', hi]
      _ = ∫ omega, plusParityPatternSpinPolynomial beta S' odd' omega ∂mu :=
        (integral_plusParityPatternSpinPolynomial_eq_multiOpenExpansion
          mu beta S' odd' hS'diag).symm
  have hsentinel : sentinel ∈ indices := by simp [indices]
  have hsentinel' : sentinel' ∈ indices := by simp [indices]
  have hvertices : Disjoint (edgeVertexSupport S)
      ((edgeVertexSupport S').image (fun x => g⁻¹ • x)) := by
    simpa [sentinel, sentinel', plusParityExpansionSupport] using
      hdisj sentinel hsentinel sentinel' hsentinel'
  have hedges : Disjoint S (currentShiftFinset g S') := by
    rw [Finset.disjoint_left]
    intro e heS heShift
    rw [currentShiftFinset, Finset.mem_image] at heShift
    obtain ⟨e', heS', heq⟩ := heShift
    have hxS' : e'.out.1 ∈ edgeVertexSupport S' :=
      mem_edgeVertexSupport_of_mem_edge heS' (Sym2.out_fst_mem e')
    have hxedge : g⁻¹ • e'.out.1 ∈ g⁻¹ • e' := by
      change g⁻¹ • e'.out.1 ∈ Sym2.map (fun x => g⁻¹ • x) e'
      exact Sym2.mem_map.mpr ⟨e'.out.1, Sym2.out_fst_mem e', rfl⟩
    rw [heq] at hxedge
    have hxS : g⁻¹ • e'.out.1 ∈ edgeVertexSupport S :=
      mem_edgeVertexSupport_of_mem_edge heS hxedge
    exact (Finset.disjoint_left.mp hvertices hxS)
      (Finset.mem_image.mpr ⟨e'.out.1, hxS', rfl⟩)
  refine ⟨g, hedges, ?_⟩
  rw [infinitePlusCurrentMeasure_parityPattern_inter_shift_real_eq_integral
      hbeta g S S' odd odd' hS hS' hedges,
    infinitePlusCurrentMeasure_parityPattern_real_eq_integral hbeta S odd hS,
    infinitePlusCurrentMeasure_parityPattern_real_eq_integral hbeta S' odd' hS']
  simpa only [hleftPoint, hrightPoint, hleftMass, hrightMass, mu] using hcorr


theorem currentMarginalPMF_eq_parity_bind_of_pattern_factor
    {E : Type*} [Countable E] [DecidableEq E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (S : Finset E) (beta : Real) (hbeta : 0 < beta)
    (hfactor : ∀ a : ↑S -> Nat,
      (mu : Measure _).real (currentCylinder S {a}) =
        (mu : Measure _).real
            (currentParityPatternCylinder S (currentLocalParity a)) *
          ENNReal.toReal
            (finiteParityPMF S beta hbeta (currentLocalParity a) a)) :
    (currentMarginal mu S : Measure (↑S -> Nat)).toPMF =
      (currentParityMarginalPMF mu S).bind
        (finiteParityPMF S beta hbeta) := by
  apply PMF.ext
  intro a
  rw [Measure.toPMF_apply, bind_finiteParityPMF_apply,
    currentMarginal_apply, currentParityMarginalPMF_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (PMF.apply_ne_top _ _))).mp
  rw [ENNReal.toReal_mul]
  simpa only [Measure.real] using hfactor a


theorem infinitePlusCurrentMarginalPMF_eq_parity_bind {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (currentMarginal (infinitePlusCurrentMeasure d beta hbeta.le) S :
        Measure (↑S -> Nat)).toPMF =
      (currentParityMarginalPMF
        (infinitePlusCurrentMeasure d beta hbeta.le) S).bind
          (finiteParityPMF S beta hbeta) := by
  apply currentMarginalPMF_eq_parity_bind_of_pattern_factor
  intro a
  have hfactor := plusCurrentLimit_pattern_factor d beta hbeta S hS
    (infiniteCurrentBoxSubsequence_strictMono d beta hbeta.le)
    (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta.le) a
  rw [Measure.real, Measure.real]
  rw [hfactor]
  rw [ENNReal.toReal_mul]

end StatMech.FrontierB
