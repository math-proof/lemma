/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
import Def.StatisticalMechanics.Code.FK.ComparisonHolley.Part3
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open StatMech


theorem reducedDensity_mem_Ioo {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    0 < reducedDensity p q ∧ reducedDensity p q < 1 := by
  have hden : 0 < p + q * (1 - p) := by nlinarith
  unfold reducedDensity
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hden]; nlinarith


theorem reducedDensity_key {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    q * reducedDensity p q * (1 - p) = (1 - reducedDensity p q) * p := by
  have hden : 0 < p + q * (1 - p) := by nlinarith
  unfold reducedDensity
  field_simp
  ring


theorem edgeFactor_bernoulli_lower_eq {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (α β : Bool) :
    (if α then reducedDensity p q else 1 - reducedDensity p q) * (if β then p else 1 - p)
        * (if (!β && α) then q else 1)
      = (if (α && β) then reducedDensity p q else 1 - reducedDensity p q)
        * (if (α || β) then p else 1 - p) := by
  have hkey : q * reducedDensity p q * (1 - p) = (1 - reducedDensity p q) * p :=
    reducedDensity_key hp hp1 hq
  cases α <;> cases β <;>
    simp only [Bool.and_self, Bool.or_self, Bool.and_false, Bool.or_false, Bool.and_true,
      Bool.or_true, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false] <;>
    linarith [hkey]


theorem edgeProduct_bernoulli_lower_eq {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    edgeProduct G (reducedDensity p q) a * edgeProduct G p b
        * ∏ e ∈ G.edgeFinset, (if (!(b e) && a e) = true then q else (1 : ℝ))
      = edgeProduct G (reducedDensity p q) (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
  unfold edgeProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hinf : (a ⊓ b) e = (a e && b e) := rfl
  have hsup : (a ⊔ b) e = (a e || b e) := rfl
  rw [hinf, hsup]
  exact edgeFactor_bernoulli_lower_eq hp hp1 hq (a e) (b e)


theorem qFactor_eq_pow (q : ℝ) (a b : ConfigSpace (Sym2 V)) :
    ∏ e ∈ G.edgeFinset, (if (!(b e) && a e) = true then q else (1 : ℝ))
      = q ^ (G.edgeFinset.filter (fun e => (!(b e) && a e) = true)).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]


theorem openCount_sup (a b : ConfigSpace (Sym2 V)) :
    chOpenCount G (a ⊔ b)
      = chOpenCount G b + (G.edgeFinset.filter (fun e => (!(b e) && a e) = true)).card := by
  unfold chOpenCount
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hG, hval⟩
      have h2 : (a ⊔ b) e = (a e || b e) := rfl
      rw [h2, Bool.or_eq_true] at hval
      by_cases hb : b e = true
      · exact Or.inl ⟨hG, hb⟩
      · rw [Bool.not_eq_true] at hb
        rcases hval with ha | hbb
        · exact Or.inr ⟨hG, by rw [hb, ha]; rfl⟩
        · exact absurd hbb (by rw [hb]; simp)
    · rintro (⟨hG, hb⟩ | ⟨hG, hcond⟩)
      · refine ⟨hG, ?_⟩
        have h2 : (a ⊔ b) e = (a e || b e) := rfl
        rw [h2, Bool.or_eq_true]; exact Or.inr hb
      · refine ⟨hG, ?_⟩
        rw [Bool.and_eq_true, Bool.not_eq_true'] at hcond
        have h2 : (a ⊔ b) e = (a e || b e) := rfl
        rw [h2, Bool.or_eq_true]; exact Or.inl hcond.2
  · rw [Finset.disjoint_left]
    rintro e he1 he2
    rw [Finset.mem_filter] at he1 he2
    rw [Bool.and_eq_true, Bool.not_eq_true'] at he2
    rw [he1.2] at he2; exact Bool.noConfusion he2.2.1


theorem numClusters_le_sup_add_opened (a b : ConfigSpace (Sym2 V)) :
    numClusters G b
      ≤ numClusters G (a ⊔ b)
        + (G.edgeFinset.filter (fun e => (!(b e) && a e) = true)).card := by
  have hcum := numClusters_add_openCount_mono G (diffSet G b (a ⊔ b)).card b (a ⊔ b)
    le_sup_right rfl
  rw [openCount_sup G a b] at hcum
  omega


theorem edgeProduct_cross_bernoulli_lower {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    edgeProduct G (reducedDensity p q) a * fkWeight G p q b
      ≤ edgeProduct G (reducedDensity p q) (a ⊓ b) * fkWeight G p q (a ⊔ b) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  set m := (G.edgeFinset.filter (fun e => (!(b e) && a e) = true)).card with hm
  
  have hqfac : ∏ e ∈ G.edgeFinset, (if (!(b e) && a e) = true then q else (1 : ℝ)) = q ^ m :=
    qFactor_eq_pow G q a b
  
  have hclust : q ^ numClusters G b ≤ q ^ numClusters G (a ⊔ b) * q ^ m := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hq (numClusters_le_sup_add_opened G a b)
  
  have hid : edgeProduct G (reducedDensity p q) a * edgeProduct G p b * q ^ m
      = edgeProduct G (reducedDensity p q) (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
    rw [← hqfac]; exact edgeProduct_bernoulli_lower_eq G hp hp1 hq a b
  
  have hp'pos := (reducedDensity_mem_Ioo hp hp1 hq).1
  have hp'lt := (reducedDensity_mem_Ioo hp hp1 hq).2
  have hEPa : 0 ≤ edgeProduct G (reducedDensity p q) a :=
    (edgeProduct_pos G hp'pos hp'lt a).le
  have hEPb : 0 ≤ edgeProduct G p b := (edgeProduct_pos G hp hp1 b).le
  
  unfold fkWeight
  calc edgeProduct G (reducedDensity p q) a * (edgeProduct G p b * q ^ numClusters G b)
      = (edgeProduct G (reducedDensity p q) a * edgeProduct G p b) * q ^ numClusters G b := by
        ring
    _ ≤ (edgeProduct G (reducedDensity p q) a * edgeProduct G p b)
          * (q ^ numClusters G (a ⊔ b) * q ^ m) :=
        mul_le_mul_of_nonneg_left hclust (mul_nonneg hEPa hEPb)
    _ = (edgeProduct G (reducedDensity p q) a * edgeProduct G p b * q ^ m)
          * q ^ numClusters G (a ⊔ b) := by ring
    _ = (edgeProduct G (reducedDensity p q) (a ⊓ b) * edgeProduct G p (a ⊔ b))
          * q ^ numClusters G (a ⊔ b) := by rw [hid]
    _ = edgeProduct G (reducedDensity p q) (a ⊓ b)
          * (edgeProduct G p (a ⊔ b) * q ^ numClusters G (a ⊔ b)) := by ring


theorem fkProb_cross_bernoulli_upper {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    fkProb G p q a * fkProb G p 1 b ≤ fkProb G p q (a ⊓ b) * fkProb G p 1 (a ⊔ b) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hZ1 : 0 < fkZ G p q := fkZ_pos G hp hp1 hq0
  have hZ2 : 0 < fkZ G p 1 := fkZ_pos G hp hp1 one_pos
  unfold fkProb
  rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2),
    fkWeight_one G p b, fkWeight_one G p (a ⊔ b)]
  exact fkWeight_cross_bernoulli_upper G hp hp1 hq a b


theorem fkProb_cross_bernoulli_lower {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    fkProb G (reducedDensity p q) 1 a * fkProb G p q b
      ≤ fkProb G (reducedDensity p q) 1 (a ⊓ b) * fkProb G p q (a ⊔ b) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hp'pos := (reducedDensity_mem_Ioo hp hp1 hq).1
  have hp'lt := (reducedDensity_mem_Ioo hp hp1 hq).2
  have hZ1 : 0 < fkZ G (reducedDensity p q) 1 := fkZ_pos G hp'pos hp'lt one_pos
  have hZ2 : 0 < fkZ G p q := fkZ_pos G hp hp1 hq0
  unfold fkProb
  rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2),
    fkWeight_one G (reducedDensity p q) a, fkWeight_one G (reducedDensity p q) (a ⊓ b)]
  exact edgeProduct_cross_bernoulli_lower G hp hp1 hq a b


theorem fk_monotone_in_p {p₁ p₂ q : ℝ} (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₂ : 0 < p₂)
    (hp₂' : p₂ < 1) (hle : p₁ ≤ p₂) (hq : 1 ≤ q) :
    measOfMass (fkProb G p₁ q) ≼ measOfMass (fkProb G p₂ q) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  refine holley_stochasticallyDominated (fun ω => fkProb_nonneg G hp₁ hp₁' hq0 ω)
    (fun ω => fkProb_nonneg G hp₂ hp₂' hq0 ω) ?_
    (fun a b => fkProb_cross G hp₁ hp₁' hp₂ hp₂' hle hq a b)
  rw [fkProb_sum_eq_one G hp₁ hp₁' hq0, fkProb_sum_eq_one G hp₂ hp₂' hq0]


theorem fk_le_bernoulli {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    measOfMass (fkProb G p q) ≼ measOfMass (fkProb G p 1) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  refine holley_stochasticallyDominated (fun ω => fkProb_nonneg G hp hp1 hq0 ω)
    (fun ω => fkProb_nonneg G hp hp1 one_pos ω) ?_
    (fun a b => fkProb_cross_bernoulli_upper G hp hp1 hq a b)
  rw [fkProb_sum_eq_one G hp hp1 hq0, fkProb_sum_eq_one G hp hp1 one_pos]


theorem bernoulli_reduced_le_fk {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    measOfMass (fkProb G (reducedDensity p q) 1) ≼ measOfMass (fkProb G p q) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hp'pos := (reducedDensity_mem_Ioo hp hp1 hq).1
  have hp'lt := (reducedDensity_mem_Ioo hp hp1 hq).2
  refine holley_stochasticallyDominated (fun ω => fkProb_nonneg G hp'pos hp'lt one_pos ω)
    (fun ω => fkProb_nonneg G hp hp1 hq0 ω) ?_
    (fun a b => fkProb_cross_bernoulli_lower G hp hp1 hq a b)
  rw [fkProb_sum_eq_one G hp'pos hp'lt one_pos, fkProb_sum_eq_one G hp hp1 hq0]


theorem fk_bernoulli_sandwich {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    measOfMass (fkProb G (reducedDensity p q) 1) ≼ measOfMass (fkProb G p q)
      ∧ measOfMass (fkProb G p q) ≼ measOfMass (fkProb G p 1) :=
  ⟨bernoulli_reduced_le_fk G hp hp1 hq, fk_le_bernoulli G hp hp1 hq⟩

end FK
end StatMech
