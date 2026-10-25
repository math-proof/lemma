/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Russo
import Theorem.StatisticalMechanics.Code.Sharpness.AizenmanBarskyUncond
import Theorem.StatisticalMechanics.Code.Sharpness.BetaReparam
import Def.StatisticalMechanics.Code.Sharpness.ABFieldDeriv
open MeasureTheory Set Finset Function
open scoped NNReal ENNReal

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

open ConfigSpace StatMech


variable {E : Type*} [Fintype E] [DecidableEq E]


lemma configWeightV_eq (p : E → ℝ) (e : E) (ω : ConfigSpace E) :
    configWeightV p ω = edgeWeightV p ω e * weightOffV p e ω := by
  unfold configWeightV weightOffV
  rw [← Finset.mul_prod_erase univ _ (mem_univ e)]


lemma weightOffV_congr (p : E → ℝ) (e : E) {ω ω' : ConfigSpace E}
    (h : ∀ e', e' ≠ e → ω e' = ω' e') : weightOffV p e ω = weightOffV p e ω' := by
  unfold weightOffV
  apply Finset.prod_congr rfl
  intro j hj
  have hje : j ≠ e := (Finset.mem_erase.mp hj).1
  unfold edgeWeightV; rw [h j hje]


lemma weightOffV_update (p : E → ℝ) (e : E) (t : ℝ) (ω : ConfigSpace E) :
    weightOffV (Function.update p e t) e ω = weightOffV p e ω := by
  unfold weightOffV
  apply Finset.prod_congr rfl
  intro j hj
  have hje : j ≠ e := (Finset.mem_erase.mp hj).1
  unfold edgeWeightV
  rw [Function.update_of_ne hje]


lemma probV_update_eq (p : E → ℝ) (e₀ : E) (t : ℝ) (A : Set (ConfigSpace E)) :
    probV (Function.update p e₀ t) A
      = ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((if ω e₀ then t else 1 - t) * weightOffV p e₀ ω) := by
  unfold probV
  apply Finset.sum_congr rfl
  intro ω _
  rw [configWeightV_eq (Function.update p e₀ t) e₀ ω, weightOffV_update]
  congr 2
  unfold edgeWeightV
  rw [Function.update_self]

omit [Fintype E] [DecidableEq E] in


lemma hasDerivAt_singleEdgeFactor (ω : ConfigSpace E) (e₀ : E) (t : ℝ) :
    HasDerivAt (fun t => if ω e₀ then t else 1 - t) (if ω e₀ then (1 : ℝ) else -1) t := by
  by_cases h : ω e₀
  · simp only [h, if_true]; exact hasDerivAt_id t
  · simp only [h]
    simpa using (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)


lemma abfd_russo_per_eta (p : E → ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (e₀ : E) (ωt ωf : ConfigSpace E)
    (hwo : weightOffV p e₀ ωt = weightOffV p e₀ ωf)
    (hto : setOpen e₀ ωt = ωt) (htc : setClosed e₀ ωt = ωf)
    (ht : ωt e₀ = true) (hf : ωf e₀ = false) :
    {ω | IsPivotal e₀ A ω}.indicator (fun _ => (1 : ℝ)) ωt * configWeightV p ωt +
        {ω | IsPivotal e₀ A ω}.indicator (fun _ => (1 : ℝ)) ωf * configWeightV p ωf =
      A.indicator (fun _ => (1 : ℝ)) ωt
          * ((if ωt e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ωt) +
        A.indicator (fun _ => (1 : ℝ)) ωf
          * ((if ωf e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ωf) := by
  classical
  have hife : (if ωt e₀ then (1 : ℝ) else -1) = 1 := by rw [ht]; rfl
  have hiff : (if ωf e₀ then (1 : ℝ) else -1) = -1 := by rw [hf]; rfl
  rw [hife, hiff, configWeightV_eq p e₀ ωt, configWeightV_eq p e₀ ωf]
  have hewt : edgeWeightV p ωt e₀ = p e₀ := by unfold edgeWeightV; rw [ht]; rfl
  have hewf : edgeWeightV p ωf e₀ = 1 - p e₀ := by unfold edgeWeightV; rw [hf]; rfl
  rw [hewt, hewf, ← hwo]
  set w := weightOffV p e₀ ωt with hw
  have hpiv_eq : IsPivotal e₀ A ωt ↔ IsPivotal e₀ A ωf := by
    apply isPivotal_congr; intro e' he'; rw [← htc, setClosed_of_ne he']
  have hpiv_t : IsPivotal e₀ A ωt ↔ (ωf ∉ A ∧ ωt ∈ A) := by
    rw [isPivotal_iff_of_isIncreasing hA, hto, htc]
  have pivInd : ∀ ω, {ω | IsPivotal e₀ A ω}.indicator (fun _ => (1 : ℝ)) ω
      = if IsPivotal e₀ A ω then 1 else 0 := fun ω => by
    rw [Set.indicator_apply]; congr 1
  rw [pivInd ωt, pivInd ωf]
  by_cases hmt : ωt ∈ A <;> by_cases hmf : ωf ∈ A
  · have hnp : ¬ IsPivotal e₀ A ωt := by rw [hpiv_t]; tauto
    rw [Set.indicator_of_mem hmt, Set.indicator_of_mem hmf, if_neg hnp,
        if_neg (hpiv_eq.not.mp hnp)]; ring
  · have hp : IsPivotal e₀ A ωt := by rw [hpiv_t]; exact ⟨hmf, hmt⟩
    rw [Set.indicator_of_mem hmt, Set.indicator_of_notMem hmf, if_pos hp,
        if_pos (hpiv_eq.mp hp)]; ring
  · exfalso
    have hle : ωf ≤ ωt := by
      have := setClosed_le_setOpen e₀ ωt; rwa [htc, hto] at this
    exact hmt (hA hle hmf)
  · have hnp : ¬ IsPivotal e₀ A ωt := by rw [hpiv_t]; tauto
    rw [Set.indicator_of_notMem hmt, Set.indicator_of_notMem hmf, if_neg hnp,
        if_neg (hpiv_eq.not.mp hnp)]; ring


lemma abfd_russo_per_edge (p : E → ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (e₀ : E) :
    ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
        * ((if ω e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ω)
      = pivotalProbV p A e₀ := by
  
  rw [← Equiv.sum_comp (Equiv.funSplitAt e₀ Bool).symm
        (fun ω => A.indicator (fun _ => (1 : ℝ)) ω
          * ((if ω e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ω))]
  unfold pivotalProbV
  rw [← Equiv.sum_comp (Equiv.funSplitAt e₀ Bool).symm
        (fun ω => (Set.indicator {ω | IsPivotal e₀ A ω} (fun _ => (1 : ℝ)) ω)
          * configWeightV p ω)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro η _
  set ωt := (Equiv.funSplitAt e₀ Bool).symm (true, η) with hωt
  set ωf := (Equiv.funSplitAt e₀ Bool).symm (false, η) with hωf
  have ht : ωt e₀ = true := by rw [hωt]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hf : ωf e₀ = false := by rw [hωf]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hto : setOpen e₀ ωt = ωt := by
    funext j
    by_cases hj : j = e₀
    · subst hj; rw [setOpen_self, ht]
    · rw [setOpen_of_ne hj]
  have htc : setClosed e₀ ωt = ωf := by
    funext j
    by_cases hj : j = e₀
    · subst hj; rw [setClosed_self, hf]
    · rw [setClosed_of_ne hj, hωt, hωf]
      simp [Equiv.funSplitAt, Equiv.piSplitAt, hj]
  have hwo : weightOffV p e₀ ωt = weightOffV p e₀ ωf := by
    apply weightOffV_congr; intro e' he'
    rw [hωt, hωf]; simp [Equiv.funSplitAt, Equiv.piSplitAt, he']
  exact (abfd_russo_per_eta p A hA e₀ ωt ωf hwo hto htc ht hf).symm


theorem hasDerivAt_probV_single (p : E → ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (e₀ : E) :
    HasDerivAt (fun t => probV (Function.update p e₀ t) A) (pivotalProbV p A e₀) (p e₀) := by
  
  have hfun : (fun t => probV (Function.update p e₀ t) A)
      = fun t => ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((if ω e₀ then t else 1 - t) * weightOffV p e₀ ω) := by
    funext t; exact probV_update_eq p e₀ t A
  rw [hfun]
  
  have hderiv : HasDerivAt
      (fun t => ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((if ω e₀ then t else 1 - t) * weightOffV p e₀ ω))
      (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((if ω e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ω)) (p e₀) := by
    apply HasDerivAt.fun_sum
    intro ω _
    have h1 : HasDerivAt (fun t => (if ω e₀ then t else 1 - t) * weightOffV p e₀ ω)
        ((if ω e₀ then (1 : ℝ) else -1) * weightOffV p e₀ ω) (p e₀) :=
      (hasDerivAt_singleEdgeFactor ω e₀ (p e₀)).mul_const _
    exact h1.const_mul (A.indicator (fun _ => (1 : ℝ)) ω)
  
  rw [← abfd_russo_per_edge p A hA e₀]
  exact hderiv


end Sharpness
end StatMech
