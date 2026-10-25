/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part4
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Def.StatisticalMechanics.Code.Ising.GHSLebowitz.Part10
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsL_fibreFactorization (β h : ℝ) (o x y : V) :
    GHSLebowitzFibreFactorization G β h o x y := by
  intro q
  let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    ghsLTWeight G β h q (ghsLTComplete q st)
  let fU : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    ghsLUWeight G β q (ghsLUComplete q su)
  let tObs : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    tvar (ghsLTComplete q st) (ghsLMate q (ghsLTComplete q st)) y
  let uuObs : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) o *
      uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) x
  have hweight (a : ConfigSpace V) : ghsLFibreWeight G β h q a =
      fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsLFibreWeight
    rw [ghsL_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsLTWeight_split, ghsLUWeight_split]
  have htobs (a : ConfigSpace V) : tvar a (ghsLMate q a) y =
      tObs (ghsLSplitEquiv q a).1 := by
    exact ghsL_tvar_split q a y
  have huuobs (a : ConfigSpace V) :
      uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x =
        uuObs (ghsLSplitEquiv q a).2 := by
    exact ghsL_uvar_mul_split q a o x
  have hUUT : ghsLFibreNumerator G β h
      (fun a b => uvar a b o * uvar a b x * tvar a b y) q =
      ∑ a : ConfigSpace V,
        (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
          (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    unfold ghsLFibreNumerator
    apply Finset.sum_congr rfl
    intro a _
    change ghsLFibreWeight G β h q a *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x *
        tvar a (ghsLMate q a) y) = _
    rw [hweight, htobs, huuobs]
    ring
  have hMass : ghsLFibreMass G β h q =
      ∑ a : ConfigSpace V,
        fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsLFibreMass
    apply Finset.sum_congr rfl
    intro a _
    exact hweight a
  have hT : ghsLFibreNumerator G β h (fun a b => tvar a b y) q =
      ∑ a : ConfigSpace V,
        (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
          fU (ghsLSplitEquiv q a).2 := by
    unfold ghsLFibreNumerator
    apply Finset.sum_congr rfl
    intro a _
    change ghsLFibreWeight G β h q a * tvar a (ghsLMate q a) y = _
    rw [hweight, htobs]
    ring
  have hUU : ghsLFibreNumerator G β h
      (fun a b => uvar a b o * uvar a b x) q =
      ∑ a : ConfigSpace V,
        fT (ghsLSplitEquiv q a).1 *
          (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    unfold ghsLFibreNumerator
    apply Finset.sum_congr rfl
    intro a _
    change ghsLFibreWeight G β h q a *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) = _
    rw [hweight, huuobs]
    ring
  have hcross := ghsL_split_cross_product (V := V) q
    (fun st => fT st * tObs st) fT
    (fun su => fU su * uuObs su) fU
  unfold ghsLFibreUU ghsLFibreT ghsLFibreExpectation
  have hm : ghsLFibreMass G β h q ≠ 0 := (ghsLFibreMass_pos G β h q).ne'
  field_simp [hm]
  rw [hUUT, hMass, hUU, hT]
  simpa [mul_comm] using hcross


theorem ghsL_duplicate_cov_nonpos_of_fibres (β h : ℝ) (o x y : V)
    (hlattice : FKGLatticeCondition (ghsLAgreementProb G β h))
    (hfactor : GHSLebowitzFibreFactorization G β h o x y)
    (huu : Antitone (ghsLFibreUU G β h o x))
    (ht : Monotone (ghsLFibreT G β h y)) :
    isingExp2 G β h (fun a b => uvar a b o * uvar a b x * tvar a b y)
      ≤ isingExp2 G β h (fun a b => uvar a b o * uvar a b x)
          * isingExp2 G β h (fun a b => tvar a b y) := by
  unfold GHSLebowitzFibreFactorization at hfactor
  have hfkg := ghsL_fkg_antitone_monotone (V := V)
    (ghsLAgreementProb_nonneg G β h) (ghsLAgreementProb_sum_eq_one G β h)
    hlattice huu ht
  rw [ghsL_isIngExp2_fibre, ghsL_isIngExp2_fibre, ghsL_isIngExp2_fibre]
  simp_rw [hfactor]
  exact hfkg


theorem ghsLFibreUU_antitone_of_eq (β h : ℝ) (hβ : 0 ≤ β) (o x : V)
    (hdict : ∀ q : ConfigSpace V,
      ghsLFibreUU G β h o x q =
        ghsvp_disagreementCorr G β o x (ghsLAgreeFinset q)) :
    Antitone (ghsLFibreUU G β h o x) := by
  intro q r hqr
  rw [hdict, hdict]
  exact ghsvp_disagreementCorr_antitone G β hβ o x
    (ghsLAgreeFinset_monotone hqr)


theorem ghsLFibreT_monotone_of_eq (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (y : V)
    (hdict : ∀ q : ConfigSpace V,
      ghsLFibreT G β h y q = ghsvp_agreementMag G β h y (ghsLAgreeFinset q)) :
    Monotone (ghsLFibreT G β h y) := by
  intro q r hqr
  rw [hdict, hdict]
  exact ghsvp_agreementMag_monotone G β h hβ hh y
    (ghsLAgreeFinset_monotone hqr)


theorem ghsL_pair_of_vertexPartition (β h c : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hc : 0 < c) (o x y : V)
    (hmass : ∀ q : ConfigSpace V,
      ghsvp_subsetMass G β h (ghsLAgreeFinset q) = c * ghsLFibreMass G β h q)
    (huu : ∀ q : ConfigSpace V,
      ghsLFibreUU G β h o x q =
        ghsvp_disagreementCorr G β o x (ghsLAgreeFinset q))
    (ht : ∀ q : ConfigSpace V,
      ghsLFibreT G β h y q = ghsvp_agreementMag G β h y (ghsLAgreeFinset q)) :
    cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) := by
  apply ghsL_pair_of_duplicate_cov_nonpos G β h o x y
  exact ghsL_duplicate_cov_nonpos_of_fibres G β h o x y
    (ghsLAgreementProb_fkg_of_subsetMass_scale G β h c hc hmass hβ hh)
    (ghsL_fibreFactorization G β h o x y)
    (ghsLFibreUU_antitone_of_eq G β h hβ o x huu)
    (ghsLFibreT_monotone_of_eq G β h hβ hh y ht)


theorem ghsLAgreementProb_fkg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    FKGLatticeCondition (ghsLAgreementProb G β h) := by
  apply ghsLAgreementProb_fkg_of_subsetMass_scale G β h
    (4 * Fintype.card (ConfigSpace V))
  · have hc : 0 < (Fintype.card (ConfigSpace V) : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ => false⟩)
    positivity
  · exact ghsvp_subsetMass_eq_card_mul_fibreMass G β h
  · exact hβ
  · exact hh


theorem ghsL_pair (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o x y : V) (hox : o ≠ x) :
    cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) := by
  apply ghsL_pair_of_vertexPartition G β h (4 * Fintype.card (ConfigSpace V)) hβ hh
  · have hc : 0 < (Fintype.card (ConfigSpace V) : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ => false⟩)
    positivity
  · exact ghsvp_subsetMass_eq_card_mul_fibreMass G β h
  · intro q
    exact ghsLFibreUU_eq_disagreementCorr G β h o x hox q
  · intro q
    exact ghsLFibreT_eq_agreementMag G β h y q


theorem ghsL_threePoint (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    GHSThreePointSym G β h o := by
  intro e he
  by_cases hoe : o ∈ e
  · exact ghsThreePoint_of_mem G β h hβ hh o e he hoe
  · induction e with
    | h x y =>
        have hox : o ≠ x := by
          intro h
          subst x
          exact hoe (by simp)
        exact ghsL_pair G β h hβ hh o x y hox


theorem ghsL_pair_of_fibres (β h : ℝ) (o x y : V)
    (hlattice : FKGLatticeCondition (ghsLAgreementProb G β h))
    (hfactor : GHSLebowitzFibreFactorization G β h o x y)
    (huu : Antitone (ghsLFibreUU G β h o x))
    (ht : Monotone (ghsLFibreT G β h y)) :
    cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) :=
  ghsL_pair_of_duplicate_cov_nonpos G β h o x y
    (ghsL_duplicate_cov_nonpos_of_fibres G β h o x y hlattice hfactor huu ht)


theorem ghsL_threePoint_of_fibres (β h : ℝ) (o : V)
    (hlattice : FKGLatticeCondition (ghsLAgreementProb G β h))
    (hfactor : ∀ x y, GHSLebowitzFibreFactorization G β h o x y)
    (huu : ∀ x, Antitone (ghsLFibreUU G β h o x))
    (ht : ∀ y, Monotone (ghsLFibreT G β h y)) :
    GHSThreePointSym G β h o := by
  intro e _
  induction e with
  | h x y => exact ghsL_pair_of_fibres G β h o x y hlattice (hfactor x y) (huu x) (ht y)

end Ising
end StatMech
