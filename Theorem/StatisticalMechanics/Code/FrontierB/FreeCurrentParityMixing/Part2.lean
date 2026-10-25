/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentParityMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenSpinMixing.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusParityPatternMixing.Part2
import Def.StatisticalMechanics.Code.FrontierB.FreeCurrentParityMixing
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation Sharpness

variable {d : Nat}

theorem plusParityPatternSpinPolynomial_eq_freeEvenExpansion {d : Nat}
    (beta : Real) (S : Finset (Sym2 (Site d))) (odd : ↑S -> Bool)
    (hS : ∀ e ∈ S, ¬ e.IsDiag) (omega : ConfigSpace (Site d)) :
    plusParityPatternSpinPolynomial beta S odd omega =
      ∑ i ∈ freeParityExpansionIndices S,
        freeParityExpansionCoeff beta S odd i *
          spinProd (freeParityExpansionSupport i) omega := by
  unfold plusParityPatternSpinPolynomial freeParityExpansionIndices
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro T hT
  have hTdiag : ∀ e ∈ T, ¬ e.IsDiag := by
    intro e he
    exact hS e (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he)
  rw [exp_neg_edgeSpinSum_eq_spinProd_sum beta T hTdiag omega,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [freeParityExpansionCoeff, freeParityExpansionSupport]
  ring

theorem integrable_spinProd_mul_shift
    (mu : Measure (ConfigSpace (Site d))) [IsFiniteMeasure mu]
    (g : Multiplicative (Site d)) (A B : Finset (Site d)) :
    Integrable (fun omega => spinProd A omega * spinProd B (shift g omega)) mu := by
  have hfun : (fun omega : ConfigSpace (Site d) =>
      spinProd A omega * spinProd B (shift g omega)) =
      fun omega => spinProd (A ∆ B.image fun x => g⁻¹ • x) omega := by
    funext omega
    rw [spinProd_shift, spinProd_mul_self]
  rw [hfun]
  exact (spinProdBCF d (A ∆ B.image fun x => g⁻¹ • x)).integrable mu


theorem infiniteFreeCurrentMeasure_parityPattern_family_pairMixing_after {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (K : Nat)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (patterns : Finset (↑S -> Bool))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ k : Nat, K ≤ k ∧
      Disjoint S (currentShiftFinset (FK.freeAxisTranslationPower hd k) S) ∧
      ∀ odd ∈ patterns, ∀ odd' ∈ patterns,
        abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
            (currentParityPatternCylinder S odd ∩
              (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹'
                currentParityPatternCylinder S odd') -
          (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentParityPatternCylinder S odd) *
            (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentParityPatternCylinder S odd')) < epsilon := by
  classical
  let I := freeParityExpansionIndices S
  let support : FreeParityExpansionIndex d -> Finset (Site d) :=
    freeParityExpansionSupport
  let expansionSupports : Finset (Finset (Site d)) := I.image support
  let edgeSupports : Finset (Finset (Site d)) := S.image Sym2.toFinset
  let supports := expansionSupports ∪ edgeSupports
  let coeff : (↑S -> Bool) -> FreeParityExpansionIndex d -> Real :=
    fun odd i => freeParityExpansionCoeff beta S odd i
  let coeffs : Finset (FreeParityExpansionIndex d -> Real) := patterns.image coeff
  let M := ∑ c ∈ coeffs, ∑ i ∈ I, |c i|
  have hM : 0 ≤ M := Finset.sum_nonneg fun c hc =>
    Finset.sum_nonneg fun i hi => abs_nonneg _
  let delta := epsilon / (M * M + 1)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hSdiag : ∀ e ∈ S, ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet (hS he)
  have hsupportEven : ∀ A ∈ supports, Even A.card := by
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hA
      change i ∈ freeParityExpansionIndices S at hi
      rw [freeParityExpansionIndices, Finset.mem_sigma] at hi
      apply edgeBoundary_card_even
      intro e he
      exact hSdiag e (Finset.mem_of_subset
        (Finset.mem_powerset.mp hi.1)
        (Finset.mem_of_subset (Finset.sdiff_subset) he))
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hA
      induction e using Sym2.inductionOn with
      | _ x y =>
          have hxy : x ≠ y := by
            simpa [Sym2.IsDiag] using hSdiag s(x, y) he
          rw [Sym2.toFinset_mk_eq, Finset.card_pair hxy]
          exact even_two
  obtain ⟨k, hkK, hparity⟩ :=
    freeInfiniteVolume_evenParity_family_pairMixing_after
      hd hbeta K supports hsupportEven delta hdelta
  let g := FK.freeAxisTranslationPower hd k
  change ∀ A ∈ supports, ∀ B ∈ supports,
    Disjoint A (B.image fun x => g⁻¹ • x) ∧
      abs ((freeInfiniteVolume d
          (p := 1 - Real.exp (-2 * beta)) (q := 2)
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            linarith)
          (by linarith [Real.exp_pos (-2 * beta)])
          (by norm_num : (0 : Real) < 2) : Measure _).real
            (allClustersEvenEvent (hypercubicLattice d)
              (A ∪ B.image fun x => g⁻¹ • x)) -
        (freeInfiniteVolume d
          (p := 1 - Real.exp (-2 * beta)) (q := 2)
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            linarith)
          (by linarith [Real.exp_pos (-2 * beta)])
          (by norm_num : (0 : Real) < 2) : Measure _).real
            (allClustersEvenEvent (hypercubicLattice d) A) *
        (freeInfiniteVolume d
          (p := 1 - Real.exp (-2 * beta)) (q := 2)
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            linarith)
          (by linarith [Real.exp_pos (-2 * beta)])
          (by norm_num : (0 : Real) < 2) : Measure _).real
            (allClustersEvenEvent (hypercubicLattice d) B)) < delta at hparity
  have hindexDisj : ∀ i ∈ I, ∀ j ∈ I,
      Disjoint (support i) ((support j).image fun x => g⁻¹ • x) := by
    intro i hi j hj
    exact (hparity (support i)
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
      (support j)
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩))).1
  have hedgeDisj : Disjoint S (currentShiftFinset g S) := by
    rw [Finset.disjoint_left]
    intro e heS heShift
    rw [currentShiftFinset, Finset.mem_image] at heShift
    obtain ⟨e', heS', heq⟩ := heShift
    have hpair := (hparity e.toFinset
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, heS, rfl⟩))
      e'.toFinset
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e', heS', rfl⟩))).1
    have hx : g⁻¹ • e'.out.1 ∈ e := by
      have hx' : g⁻¹ • e'.out.1 ∈ g⁻¹ • e' := by
        change g⁻¹ • e'.out.1 ∈ Sym2.map (fun x => g⁻¹ • x) e'
        exact Sym2.mem_map.mpr ⟨e'.out.1, Sym2.out_fst_mem e', rfl⟩
      rwa [heq] at hx'
    exact (Finset.disjoint_left.mp hpair
      (by simpa only [Sym2.mem_toFinset] using hx))
      (Finset.mem_image.mpr ⟨e'.out.1,
        by simpa only [Sym2.mem_toFinset] using Sym2.out_fst_mem e', rfl⟩)
  let spinMu := (freeState d beta 0 : Measure (ConfigSpace (Site d)))
  have hgood : ∀ i ∈ I, ∀ j ∈ I,
      abs ((∫ omega, spinProd (support i) omega *
          spinProd (support j) (shift g omega) ∂spinMu) -
        (∫ omega, spinProd (support i) omega ∂spinMu) *
          (∫ omega, spinProd (support j) omega ∂spinMu)) < delta := by
    intro i hi j hj
    have hiMem : support i ∈ supports :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have hjMem : support j ∈ supports :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    have hbase := (hparity (support i) hiMem (support j) hjMem).2
    have hiEven := hsupportEven (support i) hiMem
    have hjEven := hsupportEven (support j) hjMem
    have hdisj := hindexDisj i hi j hj
    have hunionEven : Even
        (support i ∪ (support j).image fun x => g⁻¹ • x).card := by
      rw [Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (MulAction.injective g⁻¹)]
      exact hiEven.add hjEven
    rw [← integral_freeState_spinProd_eq_freeInfinite_allClustersEven
        d beta hbeta hd _ hunionEven,
      ← integral_freeState_spinProd_eq_freeInfinite_allClustersEven
        d beta hbeta hd _ hiEven,
      ← integral_freeState_spinProd_eq_freeInfinite_allClustersEven
        d beta hbeta hd _ hjEven] at hbase
    have hjoint :
        (∫ omega, spinProd (support i) omega *
          spinProd (support j) (shift g omega) ∂spinMu) =
        ∫ omega, spinProd
          (support i ∪ (support j).image fun x => g⁻¹ • x) omega
            ∂spinMu := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [spinProd_shift, spinProd_mul_self, Finset.symmDiff_eq_union hdisj]
    rw [hjoint]
    simpa only [spinMu] using hbase
  refine ⟨k, hkK, ?_⟩
  change Disjoint S (currentShiftFinset g S) ∧ _
  refine ⟨hedgeDisj, ?_⟩
  intro odd hodd odd' hodd'
  have hc : coeff odd ∈ coeffs := Finset.mem_image.mpr ⟨odd, hodd, rfl⟩
  have hc' : coeff odd' ∈ coeffs := Finset.mem_image.mpr ⟨odd', hodd', rfl⟩
  have hcM : (∑ i ∈ I, |coeff odd i|) ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum
      (fun c hc => Finset.sum_nonneg fun i hi => abs_nonneg (c i)) hc
  have hc'M : (∑ i ∈ I, |coeff odd' i|) ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum
      (fun c hc => Finset.sum_nonneg fun i hi => abs_nonneg (c i)) hc'
  have hleftPoint (omega : ConfigSpace (Site d)) :
      (∑ i ∈ I, coeff odd i * spinProd (support i) omega) =
        plusParityPatternSpinPolynomial beta S odd omega := by
    exact (plusParityPatternSpinPolynomial_eq_freeEvenExpansion
      beta S odd hSdiag omega).symm
  have hrightPoint (omega : ConfigSpace (Site d)) :
      (∑ i ∈ I, coeff odd' i * spinProd (support i) omega) =
        plusParityPatternSpinPolynomial beta S odd' omega := by
    exact (plusParityPatternSpinPolynomial_eq_freeEvenExpansion
      beta S odd' hSdiag omega).symm
  rw [infiniteFreeCurrentMeasure_parityPattern_inter_shift_real_eq_integral
      hbeta g S S odd odd' hS hS hedgeDisj,
    infiniteFreeCurrentMeasure_parityPattern_real_eq_integral hbeta S odd hS,
    infiniteFreeCurrentMeasure_parityPattern_real_eq_integral hbeta S odd' hS]
  simp_rw [← hleftPoint, ← hrightPoint]
  have hint :
      (∫ omega, (∑ i ∈ I, coeff odd i * spinProd (support i) omega) *
          (∑ j ∈ I, coeff odd' j * spinProd (support j) (shift g omega))
        ∂spinMu) =
      ∑ i ∈ I, ∑ j ∈ I, coeff odd i * coeff odd' j *
        ∫ omega, spinProd (support i) omega *
          spinProd (support j) (shift g omega) ∂spinMu := by
    simp_rw [Finset.sum_mul_sum]
    have hpoint (i j : FreeParityExpansionIndex d)
        (omega : ConfigSpace (Site d)) :
        (coeff odd i * spinProd (support i) omega) *
          (coeff odd' j * spinProd (support j) (shift g omega)) =
        (coeff odd i * coeff odd' j) *
          (spinProd (support i) omega *
            spinProd (support j) (shift g omega)) := by ring
    simp_rw [hpoint]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [integral_const_mul]
      · intro j hj
        exact (integrable_spinProd_mul_shift spinMu g (support i) (support j)).const_mul _
    · intro i hi
      apply integrable_finsetSum
      intro j hj
      exact (integrable_spinProd_mul_shift spinMu g (support i) (support j)).const_mul _
  rw [hint, integral_finsetSum, integral_finsetSum, Finset.sum_mul_sum,
    ← Finset.sum_sub_distrib]
  · simp_rw [integral_const_mul]
    have hdiff (i : FreeParityExpansionIndex d) :
        (∑ j ∈ I, coeff odd i * coeff odd' j *
            ∫ omega, spinProd (support i) omega *
              spinProd (support j) (shift g omega) ∂spinMu) -
          ∑ j ∈ I,
            (coeff odd i * ∫ omega, spinProd (support i) omega ∂spinMu) *
              (coeff odd' j * ∫ omega, spinProd (support j) omega ∂spinMu) =
          ∑ j ∈ I, coeff odd i * coeff odd' j *
            ((∫ omega, spinProd (support i) omega *
                spinProd (support j) (shift g omega) ∂spinMu) -
              (∫ omega, spinProd (support i) omega ∂spinMu) *
                (∫ omega, spinProd (support j) omega ∂spinMu)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    change abs (∑ i ∈ I,
      ((∑ j ∈ I, coeff odd i * coeff odd' j *
          ∫ omega, spinProd (support i) omega *
            spinProd (support j) (shift g omega) ∂spinMu) -
        ∑ j ∈ I,
          (coeff odd i * ∫ omega, spinProd (support i) omega ∂spinMu) *
            (coeff odd' j * ∫ omega, spinProd (support j) omega ∂spinMu))) <
      epsilon
    rw [show (∑ i ∈ I,
        ((∑ j ∈ I, coeff odd i * coeff odd' j *
            ∫ omega, spinProd (support i) omega *
              spinProd (support j) (shift g omega) ∂spinMu) -
          ∑ j ∈ I,
            (coeff odd i * ∫ omega, spinProd (support i) omega ∂spinMu) *
              (coeff odd' j * ∫ omega, spinProd (support j) omega ∂spinMu))) =
        ∑ i ∈ I, ∑ j ∈ I, coeff odd i * coeff odd' j *
          ((∫ omega, spinProd (support i) omega *
              spinProd (support j) (shift g omega) ∂spinMu) -
            (∫ omega, spinProd (support i) omega ∂spinMu) *
              (∫ omega, spinProd (support j) omega ∂spinMu)) by
      apply Finset.sum_congr rfl
      intro i hi
      exact hdiff i]
    calc
      abs (∑ i ∈ I, ∑ j ∈ I, coeff odd i * coeff odd' j *
          ((∫ omega, spinProd (support i) omega *
              spinProd (support j) (shift g omega) ∂spinMu) -
            (∫ omega, spinProd (support i) omega ∂spinMu) *
              (∫ omega, spinProd (support j) omega ∂spinMu))) ≤
          ∑ i ∈ I, ∑ j ∈ I, |coeff odd i| * |coeff odd' j| * delta := by
        calc
          _ ≤ ∑ i ∈ I, ∑ j ∈ I, abs (coeff odd i * coeff odd' j *
              ((∫ omega, spinProd (support i) omega *
                  spinProd (support j) (shift g omega) ∂spinMu) -
                (∫ omega, spinProd (support i) omega ∂spinMu) *
                  (∫ omega, spinProd (support j) omega ∂spinMu))) := by
            apply (Finset.abs_sum_le_sum_abs _ _).trans
            apply Finset.sum_le_sum
            intro i hi
            exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            rw [abs_mul, abs_mul]
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            exact (hgood i hi j hj).le
      _ = (∑ i ∈ I, |coeff odd i|) *
          (∑ j ∈ I, |coeff odd' j|) * delta := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]
      _ ≤ (M * M) * delta := by
        apply mul_le_mul_of_nonneg_right _ hdelta.le
        exact mul_le_mul hcM hc'M
          (Finset.sum_nonneg fun i hi => abs_nonneg _) hM
      _ < epsilon := by
        dsimp [delta]
        have hne : M * M + 1 ≠ 0 := by positivity
        have hpos : 0 < epsilon / (M * M + 1) := by positivity
        calc
          M * M * (epsilon / (M * M + 1)) <
              (M * M + 1) * (epsilon / (M * M + 1)) :=
            mul_lt_mul_of_pos_right (by linarith) hpos
          _ = epsilon := mul_div_cancel₀ epsilon hne
  · intro i hi
    exact (spinProdBCF d (support i)).integrable spinMu |>.const_mul _
  · intro i hi
    exact (spinProdBCF d (support i)).integrable spinMu |>.const_mul _

theorem infiniteFreeCurrentMeasure_parityPattern_family_pairMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (patterns : Finset (↑S -> Bool))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : Multiplicative (Site d),
      Disjoint S (currentShiftFinset g S) ∧
      ∀ odd ∈ patterns, ∀ odd' ∈ patterns,
        abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
            (currentParityPatternCylinder S odd ∩
              (currentShift g) ⁻¹' currentParityPatternCylinder S odd') -
          (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentParityPatternCylinder S odd) *
            (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentParityPatternCylinder S odd')) < epsilon := by
  obtain ⟨k, hk, hdisj, hmix⟩ :=
    infiniteFreeCurrentMeasure_parityPattern_family_pairMixing_after
      hd hbeta 0 S hS patterns epsilon hepsilon
  exact ⟨FK.freeAxisTranslationPower hd k, hdisj, hmix⟩

end StatMech.FrontierB
