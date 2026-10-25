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
import Def.StatisticalMechanics.Code.Ising.GHSLebowitz.Part7
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsLFibreWeight_pos (β h : ℝ) (q a : ConfigSpace V) :
    0 < ghsLFibreWeight G β h q a :=
  mul_pos (isingWeight_pos G β h a) (isingWeight_pos G β h (ghsLMate q a))

theorem ghsLFibreMass_pos (β h : ℝ) (q : ConfigSpace V) :
    0 < ghsLFibreMass G β h q := by
  unfold ghsLFibreMass
  apply Finset.sum_pos
  · intro a _
    exact ghsLFibreWeight_pos G β h q a
  · exact Finset.univ_nonempty

theorem ghsLAgreementProb_nonneg (β h : ℝ) :
    0 ≤ ghsLAgreementProb G β h := fun q =>
  div_nonneg (ghsLFibreMass_pos G β h q).le (sq_nonneg _)


theorem ghsLAgreementProb_sum_eq_one (β h : ℝ) :
    ∑ q : ConfigSpace V, ghsLAgreementProb G β h q = 1 := by
  have hreindex := ghsL_sum_pair_xnor (V := V)
    (fun a b => isingWeight G β h a * isingWeight G β h b)
  have hmass : (∑ q : ConfigSpace V, ghsLFibreMass G β h q) = (isingZ G β h) ^ 2 := by
    unfold ghsLFibreMass ghsLFibreWeight isingZ
    rw [← hreindex]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  unfold ghsLAgreementProb
  rw [← Finset.sum_div, hmass]
  exact div_self (pow_ne_zero 2 (isingZ_ne_zero G β h))


theorem ghsLAgreementProb_fkg_of_subsetMass_scale (β h c : ℝ)
    (hc : 0 < c)
    (hscale : ∀ q : ConfigSpace V,
      ghsvp_subsetMass G β h (ghsLAgreeFinset q) = c * ghsLFibreMass G β h q)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    FKGLatticeCondition (ghsLAgreementProb G β h) := by
  intro q r
  have hsub := ghsvp_subsetMass_logSupermodular G β h hβ hh
    (ghsLAgreeFinset q) (ghsLAgreeFinset r)
  rw [← ghsLAgreeFinset_sup, ← ghsLAgreeFinset_inf] at hsub
  simp_rw [hscale] at hsub
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hfibre : ghsLFibreMass G β h q * ghsLFibreMass G β h r ≤
      ghsLFibreMass G β h (q ⊔ r) * ghsLFibreMass G β h (q ⊓ r) := by
    nlinarith [hsub]
  unfold ghsLAgreementProb
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_le_div_of_nonneg_right hfibre (mul_nonneg (sq_nonneg _) (sq_nonneg _))


theorem ghsLTWeight_eq_wJ_restricted (β h : ℝ) (q a : ConfigSpace V) :
    ghsLTWeight G β h q a =
      Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun _ => 2 * β)
        (fun x => if x ∈ ghsLAgreeFinset q then 2 * β * h else 0) a := by
  unfold Sharpness.wJ ghsLTWeight
  congr 1
  have hb : (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q),
      (2 * β) * bond a e) =
      2 * β * ∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), bond a e := by
    rw [Finset.mul_sum]
  have hf : (∑ x : V,
      (if x ∈ ghsLAgreeFinset q then 2 * β * h else 0) * spin a x) =
      2 * β * h * ∑ x ∈ ghsLAgreeFinset q, spin a x := by
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.mul_sum]
    unfold ghsLAgreeFinset
    apply Finset.sum_congr
    · ext x
      simp
    · simp
  rw [hb, hf]
  ring


theorem ghsLUWeight_eq_wJ (β : ℝ) (q a : ConfigSpace V) :
    ghsLUWeight G β q a =
      Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ)
        (fun _ => 2 * β) (fun _ => 0) a := by
  unfold ghsLUWeight Sharpness.wJ
  congr 1
  simp
  rw [Finset.mul_sum]


theorem ghsvp_subsetMass_eq_card_mul_fibreMass (β h : ℝ) (q : ConfigSpace V) :
    ghsvp_subsetMass G β h (ghsLAgreeFinset q) =
      (4 * Fintype.card (ConfigSpace V)) * ghsLFibreMass G β h q := by
  let T := (v : {v : V // q v = true}) → Bool
  let U := (v : {v : V // ¬ q v = true}) → Bool
  let fT : T → ℝ := fun st => ghsLTWeight G β h q (ghsLTComplete q st)
  let fU : U → ℝ := fun su => ghsLUWeight G β q (ghsLUComplete q su)
  have hmass : ghsLFibreMass G β h q =
      (∑ st : T, fT st) * ∑ su : U, fU su := by
    unfold ghsLFibreMass ghsLFibreWeight
    calc
      (∑ a : ConfigSpace V,
          isingWeight G β h a * isingWeight G β h (ghsLMate q a)) =
          ∑ a : ConfigSpace V,
            fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [ghsL_duplicateWeight_eq_tWeight_mul_uWeight,
          ghsLTWeight_split, ghsLUWeight_split]
      _ = _ := ghsL_split_sum_product q fT fU
  have ht : ghsvp_tZ G β h (ghsLAgreeFinset q) =
      (∑ st : T, fT st) * Fintype.card U := by
    unfold ghsvp_tZ Sharpness.ZJ
    have hs := ghsL_split_sum_product (V := V) q fT (fun _ : U => (1 : ℝ))
    rw [show (∑ a : ConfigSpace V,
        Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
          (fun _ => 2 * β)
          (fun x => if x ∈ ghsLAgreeFinset q then 2 * β * h else 0) a) =
        ∑ a : ConfigSpace V, fT (ghsLSplitEquiv q a).1 * (1 : ℝ) by
      apply Finset.sum_congr rfl
      intro a _
      rw [← ghsLTWeight_eq_wJ_restricted, ghsLTWeight_split]
      simp [fT]]
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hs
  have hu : ghsvp_uZ G β (ghsLAgreeFinset q)ᶜ =
      Fintype.card T * ∑ su : U, fU su := by
    unfold ghsvp_uZ Sharpness.ZJ
    have hs := ghsL_split_sum_product (V := V) q (fun _ : T => (1 : ℝ)) fU
    rw [show (∑ a : ConfigSpace V,
        Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ)
          (fun _ => 2 * β) (fun _ => 0) a) =
        ∑ a : ConfigSpace V, (1 : ℝ) * fU (ghsLSplitEquiv q a).2 by
      apply Finset.sum_congr rfl
      intro a _
      rw [← ghsLUWeight_eq_wJ, ghsLUWeight_split]
      simp [fU]]
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hs
  have hcard : Fintype.card (ConfigSpace V) = Fintype.card T * Fintype.card U := by
    rw [Fintype.card_congr (ghsLSplitEquiv q), Fintype.card_prod]
  rw [ghsvp_subsetMass_eq_four_mul_tZ_uZ, ht, hu, hmass, hcard]
  norm_num [Nat.cast_mul]
  ring


theorem ghsL_isIngExp2_fibre (β h : ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp2 G β h F =
      ∑ q : ConfigSpace V,
        ghsLAgreementProb G β h q * ghsLFibreExpectation G β h F q := by
  unfold isingExp2
  rw [ghsL_sum_pair_xnor]
  apply Finset.sum_congr rfl
  intro q _
  have hm : ghsLFibreMass G β h q ≠ 0 := (ghsLFibreMass_pos G β h q).ne'
  have hZ : isingZ G β h ≠ 0 := isingZ_ne_zero G β h
  have hlhs :
      (∑ a : ConfigSpace V,
          isingProb G β h a * isingProb G β h (ghsLMate q a) * F a (ghsLMate q a))
        = ghsLFibreNumerator G β h F q / (isingZ G β h) ^ 2 := by
    unfold ghsLFibreNumerator
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    unfold isingProb ghsLFibreWeight
    field_simp [hZ]
  rw [hlhs]
  unfold ghsLAgreementProb ghsLFibreExpectation
  field_simp [hm, hZ]


@[simp] theorem ghsLFibreExpectation_const (β h r : ℝ) (q : ConfigSpace V) :
    ghsLFibreExpectation G β h (fun _ _ => r) q = r := by
  unfold ghsLFibreExpectation ghsLFibreNumerator ghsLFibreMass
  have hm : (∑ a : ConfigSpace V, ghsLFibreWeight G β h q a) ≠ 0 :=
    (ghsLFibreMass_pos G β h q).ne'
  rw [← Finset.sum_mul]
  field_simp


theorem ghsL_fkg_antitone_monotone {π : ConfigSpace V → ℝ}
    (hπ₀ : 0 ≤ π) (hnorm : ∑ q, π q = 1) (hπ : FKGLatticeCondition π)
    {f g : ConfigSpace V → ℝ} (hf : Antitone f) (hg : Monotone g) :
    (∑ q, π q * (f q * g q))
      ≤ (∑ q, π q * f q) * (∑ q, π q * g q) := by
  have hneg : Monotone (fun q => -f q) := fun q r hqr => neg_le_neg (hf hqr)
  have h := fkg_inequality hπ₀ hnorm hπ hneg hg
  have h₁ : (∑ q, π q * -f q) = -(∑ q, π q * f q) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have h₂ : (∑ q, π q * (-f q * g q)) = -(∑ q, π q * (f q * g q)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [h₁, h₂] at h
  linarith


end Ising
end StatMech
