/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentParityMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenSpinMixing.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusParityPatternMixing.Part2
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation Sharpness

variable {d : Nat}

theorem even_card_symmDiff {V : Type*} [DecidableEq V]
    (A B : Finset V) (hA : Even A.card) (hB : Even B.card) :
    Even (A ∆ B).card := by
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rw [Finset.mem_sdiff] at hxA hxB
    exact hxB.2 hxA.1
  have hcard : (A ∆ B).card = (A \ B).card + (B \ A).card := by
    rw [show A ∆ B = (A \ B) ∪ (B \ A) by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
      ]
    exact Finset.card_union_of_disjoint hdisj
  rcases hA with ⟨a, ha⟩
  rcases hB with ⟨b, hb⟩
  have hAcard := Finset.card_sdiff_add_card_inter A B
  have hBcard := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hBcard
  refine ⟨a + b - (A ∩ B).card, ?_⟩
  omega

theorem edgeBoundary_card_even {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    Even (edgeBoundary F).card := by
  classical
  induction F using Finset.induction with
  | empty => simp [edgeBoundary]
  | @insert e F he ih =>
      have hediag : ¬ e.IsDiag := hF e (Finset.mem_insert_self e F)
      have hF' : ∀ f ∈ F, ¬ f.IsDiag :=
        fun f hf => hF f (Finset.mem_insert_of_mem hf)
      have hedge : Even e.toFinset.card := by
        induction e using Sym2.inductionOn with
        | _ x y =>
            have hxy : x ≠ y := by simpa [Sym2.IsDiag] using hediag
            rw [Sym2.toFinset_mk_eq, Finset.card_pair hxy]
            exact even_two
      rw [edgeBoundary, Finset.fold_insert he]
      exact even_card_symmDiff _ _ hedge (ih hF')

theorem infiniteFreeCurrentMeasure_parityAvoid_real_eq {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityAvoidCylinder F) =
      (∫ omega, Real.exp (-beta * edgeSpinSum F omega)
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
          Real.cosh beta ^ F.card := by
  rw [Measure.real,
    infiniteFreeCurrentMeasure_parityAvoid_eq d beta hbeta F hF,
    ENNReal.toReal_ofReal]
  positivity


theorem infiniteFreeCurrentMeasure_parityAvoid_inter_shift_real_eq {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (g : Multiplicative (Site d))
    (F F' : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hF' : (↑F' : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hdisj : Disjoint F (currentShiftFinset g F')) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityAvoidCylinder F ∩
          (currentShift g) ⁻¹' currentParityAvoidCylinder F') =
      (∫ omega, Real.exp (-beta * edgeSpinSum F omega) *
          Real.exp (-beta * edgeSpinSum F' (shift g omega))
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
        (Real.cosh beta ^ F.card * Real.cosh beta ^ F'.card) := by
  let G := currentShiftFinset g F'
  have hG : (↑G : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet :=
    currentShiftFinset_lattice d g F' hF'
  have hFG : (↑(F ∪ G) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
    intro e he
    change e ∈ F ∪ G at he
    exact (Finset.mem_union.mp he).elim (fun h => hF h) (fun h => hG h)
  rw [preimage_currentParityAvoidCylinder_currentShift,
    currentParityAvoidCylinder_inter,
    infiniteFreeCurrentMeasure_parityAvoid_real_eq hbeta (F ∪ G) hFG]
  have hcard : (F ∪ G).card = F.card + F'.card := by
    rw [Finset.card_union_of_disjoint hdisj]
    congr 1
    dsimp [G, currentShiftFinset]
    rw [Finset.card_image_of_injective _ (MulAction.injective g⁻¹)]
  have hint (omega : ConfigSpace (Site d)) :
      Real.exp (-beta * edgeSpinSum (F ∪ G) omega) =
        Real.exp (-beta * edgeSpinSum F omega) *
          Real.exp (-beta * edgeSpinSum F' (shift g omega)) := by
    rw [edgeSpinSum_union hdisj, edgeSpinSum_shift]
    rw [show -beta * (edgeSpinSum F omega + edgeSpinSum G omega) =
        -beta * edgeSpinSum F omega + -beta * edgeSpinSum G omega by ring,
      Real.exp_add]
  rw [show (∫ omega, Real.exp (-beta * edgeSpinSum (F ∪ G) omega)
      ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) =
      ∫ omega, Real.exp (-beta * edgeSpinSum F omega) *
        Real.exp (-beta * edgeSpinSum F' (shift g omega))
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) by
      apply integral_congr_ae
      filter_upwards with omega
      exact hint omega]
  rw [hcard, pow_add]


theorem infiniteFreeCurrentMeasure_parityPattern_real_eq_integral {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d))) (odd : ↑S -> Bool)
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityPatternCylinder S odd) =
      ∫ omega, plusParityPatternSpinPolynomial beta S odd omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
  rw [currentParityPattern_real_eq_avoid_sum]
  unfold plusParityPatternSpinPolynomial
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T hT
    rw [integral_const_mul]
    rw [infiniteFreeCurrentMeasure_parityAvoid_real_eq hbeta T]
    · ring
    · intro e he
      exact hS (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he)
  · intro T hT
    apply Integrable.const_mul
    have hTdiag : ∀ e ∈ T, ¬ e.IsDiag := by
      intro e he
      exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet
        (hS (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he))
    have hexp : (fun omega : ConfigSpace (Site d) =>
        Real.exp (-beta * edgeSpinSum T omega)) =
        fun omega => ∑ U ∈ T.powerset,
          edgeExpansionCoeff beta T U * spinProd (edgeBoundary (T \ U)) omega := by
      funext omega
      exact exp_neg_edgeSpinSum_eq_spinProd_sum beta T hTdiag omega
    rw [hexp]
    apply integrable_finsetSum
    intro U hU
    exact ((spinProdBCF d (edgeBoundary (T \ U))).integrable
      (freeState d beta 0 : Measure (ConfigSpace (Site d)))).const_mul _


theorem infiniteFreeCurrentMeasure_parityPattern_inter_shift_real_eq_integral
    {d : Nat} {beta : Real} (hbeta : 0 < beta)
    (g : Multiplicative (Site d))
    (S S' : Finset (Sym2 (Site d))) (odd : ↑S -> Bool) (odd' : ↑S' -> Bool)
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hS' : (↑S' : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hdisj : Disjoint S (currentShiftFinset g S')) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityPatternCylinder S odd ∩
          (currentShift g) ⁻¹' currentParityPatternCylinder S' odd') =
      ∫ omega, plusParityPatternSpinPolynomial beta S odd omega *
        plusParityPatternSpinPolynomial beta S' odd' (shift g omega)
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
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
      (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
          (currentParityAvoidCylinder T ∩
            (currentShift g) ⁻¹' currentParityAvoidCylinder U) =
        (∫ omega, Real.exp (-beta * edgeSpinSum T omega) *
            Real.exp (-beta * edgeSpinSum U (shift g omega))
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
          (Real.cosh beta ^ T.card * Real.cosh beta ^ U.card) := by
    apply infiniteFreeCurrentMeasure_parityAvoid_inter_shift_real_eq
      hbeta g T U
    · intro e he
      exact hS (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he)
    · intro e he
      exact hS' (Finset.mem_of_subset (Finset.mem_powerset.mp hU) he)
    · apply hdisj.mono (Finset.mem_powerset.mp hT)
      unfold currentShiftFinset
      exact Finset.image_mono (fun e => g⁻¹ • e)
        (Finset.mem_powerset.mp hU)
  rw [show (∑ T ∈ S.powerset, ∑ U ∈ S'.powerset,
      currentParityTraceCoeff S odd T * currentParityTraceCoeff S' odd' U *
        (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
          (currentParityAvoidCylinder T ∩
            (currentShift g) ⁻¹' currentParityAvoidCylinder U)) =
      ∑ T ∈ S.powerset, ∑ U ∈ S'.powerset,
      currentParityTraceCoeff S odd T * currentParityTraceCoeff S' odd' U *
        ((∫ omega, Real.exp (-beta * edgeSpinSum T omega) *
            Real.exp (-beta * edgeSpinSum U (shift g omega))
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
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
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T hT
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro U hU
      rw [integral_const_mul, integral_mul_const]
    · intro U hU
      apply Integrable.const_mul
      apply Integrable.mul_const
      exact integrable_exp_neg_edgeSpinSum_mul_shift
        (freeState d beta 0 : Measure (ConfigSpace (Site d))) beta g T U
          (hTdiag T hT) (hUdiag U hU)
  · intro T hT
    apply integrable_finsetSum
    intro U hU
    apply Integrable.const_mul
    apply Integrable.mul_const
    exact integrable_exp_neg_edgeSpinSum_mul_shift
      (freeState d beta 0 : Measure (ConfigSpace (Site d))) beta g T U
        (hTdiag T hT) (hUdiag U hU)

end StatMech.FrontierB
