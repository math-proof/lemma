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
import Def.StatisticalMechanics.Code.Ising.GHSLebowitz.Part8
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsLUWeight_pos (β : ℝ) (q a : ConfigSpace V) :
    0 < ghsLUWeight G β q a := by
  unfold ghsLUWeight
  positivity

theorem ghsLTWeight_pos (β h : ℝ) (q a : ConfigSpace V) :
    0 < ghsLTWeight G β h q a := by
  unfold ghsLTWeight
  positivity


theorem ghsLFibreUU_eq_uExpectation (β h : ℝ) (o x : V) (q : ConfigSpace V) :
    ghsLFibreUU G β h o x q = ghsLUExpectation G β q
      (fun a => uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) := by
  let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    ghsLTWeight G β h q (ghsLTComplete q st)
  let fU : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    ghsLUWeight G β q (ghsLUComplete q su)
  let uuObs : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) o *
      uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) x
  have hM : ghsLFibreMass G β h q = ∑ a : ConfigSpace V,
      fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsLFibreMass ghsLFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsL_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsLTWeight_split, ghsLUWeight_split]
  have hN : ghsLFibreNumerator G β h
      (fun a b => uvar a b o * uvar a b x) q = ∑ a : ConfigSpace V,
      fT (ghsLSplitEquiv q a).1 *
        (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    unfold ghsLFibreNumerator ghsLFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    change (isingWeight G β h a * isingWeight G β h (ghsLMate q a)) *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) = _
    rw [ghsL_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsLTWeight_split, ghsLUWeight_split, ghsL_uvar_mul_split]
    ring
  have hZU : (∑ a : ConfigSpace V, ghsLUWeight G β q a) =
      ∑ a : ConfigSpace V, (1 : ℝ) * fU (ghsLSplitEquiv q a).2 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsLUWeight_split]
    simp [fU]
  have hNU : (∑ a : ConfigSpace V, ghsLUWeight G β q a *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x)) =
      ∑ a : ConfigSpace V, (1 : ℝ) *
        (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsLUWeight_split, ghsL_uvar_mul_split]
    ring
  have hcross := ghsL_split_cross_product (V := V) q fT (fun _ => (1 : ℝ))
    (fun su => fU su * uuObs su) fU
  unfold ghsLFibreUU ghsLFibreExpectation ghsLUExpectation
  have hm : ghsLFibreMass G β h q ≠ 0 := (ghsLFibreMass_pos G β h q).ne'
  have hu : (∑ a : ConfigSpace V, ghsLUWeight G β q a) ≠ 0 := by
    exact (Finset.sum_pos (fun a _ => ghsLUWeight_pos G β q a) Finset.univ_nonempty).ne'
  field_simp [hm, hu]
  rw [hN, hM, hZU]
  rw [show (∑ x_1, ghsLUWeight G β q x_1 * uvar x_1 (ghsLMate q x_1) o *
      uvar x_1 (ghsLMate q x_1) x) =
      ∑ a : ConfigSpace V, (1 : ℝ) *
        (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) by
        simpa [mul_assoc] using hNU]
  simpa [mul_comm] using hcross


theorem ghsLFibreUU_eq_disagreementCorr (β h : ℝ) (o x : V) (hox : o ≠ x)
    (q : ConfigSpace V) :
    ghsLFibreUU G β h o x q =
      ghsvp_disagreementCorr G β o x (ghsLAgreeFinset q) := by
  rw [ghsLFibreUU_eq_uExpectation]
  by_cases ho : o ∈ ghsLAgreeFinset q
  · have hqo : q o = true := (mem_ghsLAgreeFinset q o).mp ho
    unfold ghsLUExpectation ghsvp_disagreementCorr
    rw [if_pos (Or.inl ho)]
    simp_rw [ghsL_uvar_mate, if_pos hqo, zero_mul, mul_zero]
    simp
  · by_cases hx : x ∈ ghsLAgreeFinset q
    · have hqx : q x = true := (mem_ghsLAgreeFinset q x).mp hx
      unfold ghsLUExpectation ghsvp_disagreementCorr
      rw [if_pos (Or.inr hx)]
      simp_rw [ghsL_uvar_mate, if_pos hqx, mul_zero]
      simp
    · have hqo : ¬ q o = true := fun h => ho ((mem_ghsLAgreeFinset q o).mpr h)
      have hqx : ¬ q x = true := fun h => hx ((mem_ghsLAgreeFinset q x).mpr h)
      unfold ghsLUExpectation ghsvp_disagreementCorr ghsvp_vertexCorr Sharpness.expJ
      rw [if_neg (not_or_intro ho hx)]
      apply congrArg₂ (· / ·)
      · apply Finset.sum_congr rfl
        intro a _
        rw [ghsLUWeight_eq_wJ]
        simp only [ghsL_uvar_mate, if_neg hqo, if_neg hqx]
        unfold spinProd
        rw [Finset.prod_pair hox]
        ring
      · apply Finset.sum_congr rfl
        intro a _
        rw [ghsLUWeight_eq_wJ]


theorem ghsLFibreT_eq_tExpectation (β h : ℝ) (y : V) (q : ConfigSpace V) :
    ghsLFibreT G β h y q = ghsLTExpectation G β h q
      (fun a => tvar a (ghsLMate q a) y) := by
  let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    ghsLTWeight G β h q (ghsLTComplete q st)
  let fU : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    ghsLUWeight G β q (ghsLUComplete q su)
  let tObs : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    tvar (ghsLTComplete q st) (ghsLMate q (ghsLTComplete q st)) y
  have hM : ghsLFibreMass G β h q = ∑ a : ConfigSpace V,
      fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsLFibreMass ghsLFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsL_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsLTWeight_split, ghsLUWeight_split]
  have hN : ghsLFibreNumerator G β h (fun a b => tvar a b y) q =
      ∑ a : ConfigSpace V,
        (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
          fU (ghsLSplitEquiv q a).2 := by
    unfold ghsLFibreNumerator ghsLFibreWeight
    apply Finset.sum_congr rfl
    intro a _
    change (isingWeight G β h a * isingWeight G β h (ghsLMate q a)) *
      tvar a (ghsLMate q a) y = _
    rw [ghsL_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsLTWeight_split, ghsLUWeight_split, ghsL_tvar_split]
    ring
  have hZT : (∑ a : ConfigSpace V, ghsLTWeight G β h q a) =
      ∑ a : ConfigSpace V, fT (ghsLSplitEquiv q a).1 * (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsLTWeight_split]
    simp [fT]
  have hNT : (∑ a : ConfigSpace V, ghsLTWeight G β h q a *
      tvar a (ghsLMate q a) y) = ∑ a : ConfigSpace V,
      (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) * (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [ghsLTWeight_split, ghsL_tvar_split]
    simp [fT, tObs]
  have hcross := ghsL_split_cross_product (V := V) q
    (fun st => fT st * tObs st) fT (fun _ => (1 : ℝ)) fU
  unfold ghsLFibreT ghsLFibreExpectation ghsLTExpectation
  have hm : ghsLFibreMass G β h q ≠ 0 := (ghsLFibreMass_pos G β h q).ne'
  have ht : (∑ a : ConfigSpace V, ghsLTWeight G β h q a) ≠ 0 := by
    exact (Finset.sum_pos (fun a _ => ghsLTWeight_pos G β h q a) Finset.univ_nonempty).ne'
  field_simp [hm, ht]
  rw [hN, hM, hZT, hNT]
  simpa [mul_comm] using hcross.symm


end Ising
end StatMech
