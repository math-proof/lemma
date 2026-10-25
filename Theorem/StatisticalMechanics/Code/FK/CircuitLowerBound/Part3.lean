/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.FK.CircuitLowerBound.Part2
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem agreeWeightSum_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (γ : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    0 < agreeWeightSum G p q γ ψ := by
  unfold agreeWeightSum
  exact Finset.sum_pos (fun σ _ => fkWeight_pos G hp hp1 hq σ) ⟨ψ, by simp⟩


theorem agreeWeightSum_insert (p q : ℝ) {e : Sym2 V} {γ : Finset (Sym2 V)} (he : e ∉ γ)
    (ψ : ConfigSpace (Sym2 V)) :
    agreeWeightSum G p q (insert e γ) ψ
      = agreeWeightSum G p q γ (setClosed e ψ) + agreeWeightSum G p q γ (setOpen e ψ) := by
  classical
  unfold agreeWeightSum
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun σ => σ e = false)]
  congr 1
  · apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hfree, h0⟩
      intro e' he'
      by_cases hee : e' = e
      · subst hee; rw [h0, setClosed_self]
      · rw [setClosed_of_ne hee]; exact hfree e' (by simp [Finset.mem_insert, hee, he'])
    · intro hfree
      refine ⟨fun e' he' => ?_, ?_⟩
      · have hne : e' ≠ e := fun h => he' (h ▸ Finset.mem_insert_self e γ)
        have := hfree e' (fun hc => he' (Finset.mem_insert_of_mem hc))
        rwa [setClosed_of_ne hne] at this
      · have := hfree e (by simpa using he)
        rwa [setClosed_self] at this
  · apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_false]
    constructor
    · rintro ⟨hfree, h1⟩
      intro e' he'
      by_cases hee : e' = e
      · subst hee; rw [h1, setOpen_self]
      · rw [setOpen_of_ne hee]; exact hfree e' (by simp [Finset.mem_insert, hee, he'])
    · intro hfree
      refine ⟨fun e' he' => ?_, ?_⟩
      · have hne : e' ≠ e := fun h => he' (h ▸ Finset.mem_insert_self e γ)
        have := hfree e' (fun hc => he' (Finset.mem_insert_of_mem hc))
        rwa [setOpen_of_ne hne] at this
      · have := hfree e (by simpa using he)
        rwa [setOpen_self] at this


theorem agreeWeightSum_empty (p q : ℝ) (ψ : ConfigSpace (Sym2 V)) :
    agreeWeightSum G p q ∅ ψ = fkWeight G p q ψ := by
  classical
  unfold agreeWeightSum
  rw [show (Finset.univ.filter
      (fun σ : ConfigSpace (Sym2 V) => ∀ e' ∉ (∅ : Finset (Sym2 V)), σ e' = ψ e')) = {ψ}
      from ?_]
  · simp
  · ext σ
    simp only [Finset.notMem_empty, not_false_eq_true, forall_const, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; funext e'; exact h e'
    · rintro rfl; intro e'; rfl


theorem cFE_pow_mul_agreeWeightSum_le {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (γ : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    cFE p q ^ γ.card * agreeWeightSum G p q γ ψ ≤ fkWeight G p q (closeAllOn γ ψ) := by
  classical
  induction γ using Finset.induction generalizing ψ with
  | empty =>
    rw [Finset.card_empty, pow_zero, one_mul, agreeWeightSum_empty]
    
    have : closeAllOn (∅ : Finset (Sym2 V)) ψ = ψ := by funext x; simp [closeAllOn]
    rw [this]
  | @insert e γ he ih =>
    rw [Finset.card_insert_of_notMem he, pow_succ, agreeWeightSum_insert G p q he]
    have hcfe_nonneg : (0 : ℝ) ≤ cFE p q := (cFE_pos hp hp1 hq).le
    
    have ihc := ih (setClosed e ψ)
    have iho := ih (setOpen e ψ)
    
    have hc : fkWeight G p q (closeAllOn γ (setClosed e ψ))
        = fkWeight G p q (setClosed e (closeAllOn γ ψ)) := by rw [closeAllOn_setClosed he]
    have ho : fkWeight G p q (closeAllOn γ (setOpen e ψ))
        = fkWeight G p q (setOpen e (closeAllOn γ ψ)) := by rw [closeAllOn_setOpen he]
    
    have htarget : closeAllOn (insert e γ) ψ = setClosed e (closeAllOn γ ψ) := by
      funext x
      by_cases hx : x = e
      · subst hx; simp [closeAllOn, setClosed_self]
      · rw [setClosed_of_ne hx]
        simp only [closeAllOn, Finset.mem_insert, hx, false_or]
    rw [htarget]
    calc cFE p q ^ γ.card * cFE p q
            * (agreeWeightSum G p q γ (setClosed e ψ) + agreeWeightSum G p q γ (setOpen e ψ))
        = cFE p q * (cFE p q ^ γ.card * agreeWeightSum G p q γ (setClosed e ψ)
              + cFE p q ^ γ.card * agreeWeightSum G p q γ (setOpen e ψ)) := by ring
      _ ≤ cFE p q * (fkWeight G p q (closeAllOn γ (setClosed e ψ))
              + fkWeight G p q (closeAllOn γ (setOpen e ψ))) := by
            apply mul_le_mul_of_nonneg_left _ hcfe_nonneg
            exact add_le_add ihc iho
      _ = cFE p q * (fkWeight G p q (setClosed e (closeAllOn γ ψ))
              + fkWeight G p q (setOpen e (closeAllOn γ ψ))) := by rw [hc, ho]
      _ = cFE p q * (fkWeight G p q (setOpen e (closeAllOn γ ψ))
              + fkWeight G p q (setClosed e (closeAllOn γ ψ))) := by ring
      _ ≤ fkWeight G p q (setClosed e (closeAllOn γ ψ)) :=
            fkWeight_setClosed_ge G hp hp1 hq e (closeAllOn γ ψ)


theorem cFE_pow_le_condClosedOn {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (γ : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    cFE p q ^ γ.card ≤ fkWeight G p q (closeAllOn γ ψ) / agreeWeightSum G p q γ ψ := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  rw [le_div_iff₀ (agreeWeightSum_pos G hp hp1 hq0 γ ψ)]
  exact cFE_pow_mul_agreeWeightSum_le G hp hp1 hq γ ψ


end FK
end StatMech
