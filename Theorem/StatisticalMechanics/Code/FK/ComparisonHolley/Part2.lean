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
import Def.StatisticalMechanics.Code.FK.ComparisonHolley.Part2
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open StatMech


theorem openSub_eq_of_diffSet_empty {b c : ConfigSpace (Sym2 V)} (hle : b ≤ c)
    (hempty : diffSet G b c = ∅) : openSub G b = openSub G c := by
  ext x y
  rw [openSub_adj, openSub_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    have := hle s(x, y); rw [hopen] at this; exact le_antisymm (by simp) this
  · rintro ⟨hadj, hopen⟩
    refine ⟨hadj, ?_⟩
    by_contra hbf
    rw [Bool.not_eq_true] at hbf
    have hmem : s(x, y) ∈ diffSet G b c := by
      unfold diffSet
      rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
      exact ⟨hadj, hbf, hopen⟩
    rw [hempty] at hmem
    exact absurd hmem (Finset.notMem_empty _)


theorem setOpen_le_of_mem_diffSet {b c : ConfigSpace (Sym2 V)} (hle : b ≤ c) {e : Sym2 V}
    (hmem : e ∈ diffSet G b c) : setOpen e b ≤ c := by
  intro e'
  by_cases h : e' = e
  · rw [h, setOpen_self]
    unfold diffSet at hmem; rw [Finset.mem_filter] at hmem
    rw [hmem.2.2]
  · rw [setOpen_of_ne h]; exact hle e'


theorem diffSet_setOpen {b c : ConfigSpace (Sym2 V)} {e : Sym2 V}
    (hmem : e ∈ diffSet G b c) :
    diffSet G (setOpen e b) c = (diffSet G b c).erase e := by
  unfold diffSet
  ext e'
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hG, hclosed, hopen⟩
    have hne : e' ≠ e := by
      rintro rfl; rw [setOpen_self] at hclosed; exact Bool.noConfusion hclosed
    rw [setOpen_of_ne hne] at hclosed
    exact ⟨hne, hG, hclosed, hopen⟩
  · rintro ⟨hne, hG, hclosed, hopen⟩
    rw [setOpen_of_ne hne]
    exact ⟨hG, hclosed, hopen⟩


theorem numClusters_add_openCount_mono : ∀ (n : ℕ) (b c : ConfigSpace (Sym2 V)),
    b ≤ c → (diffSet G b c).card = n →
    numClusters G b + chOpenCount G b ≤ numClusters G c + chOpenCount G c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b c hle hcard
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hempty : diffSet G b c = ∅ := Finset.card_eq_zero.mp hcard
      have hsub := openSub_eq_of_diffSet_empty G hle hempty
      have hk : numClusters G b = numClusters G c := numClusters_congr_openSub G hsub
      have ho : chOpenCount G b = chOpenCount G c := by
        unfold chOpenCount
        congr 1
        ext e
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hG, hval⟩
          refine ⟨hG, ?_⟩
          have := hle e; rw [hval] at this; exact le_antisymm (by simp) this
        · rintro ⟨hG, hval⟩
          refine ⟨hG, ?_⟩
          by_contra hbf
          rw [Bool.not_eq_true] at hbf
          have : e ∈ diffSet G b c := by
            unfold diffSet; rw [Finset.mem_filter]; exact ⟨hG, hbf, hval⟩
          rw [hempty] at this; exact absurd this (Finset.notMem_empty _)
      omega
    · have hne : (diffSet G b c).Nonempty := by
        rw [← Finset.card_pos, hcard]; exact hn
      obtain ⟨e, hemem⟩ := hne
      have heG : e ∈ G.edgeFinset := by
        unfold diffSet at hemem; rw [Finset.mem_filter] at hemem; exact hemem.1
      have hbe : b e = false := by
        unfold diffSet at hemem; rw [Finset.mem_filter] at hemem; exact hemem.2.1
      set b' := setOpen e b with hb'
      have hbb' : b ≤ b' := by
        rw [hb']
        intro e'
        by_cases h : e' = e
        · rw [h, setOpen_self, hbe]; simp
        · rw [setOpen_of_ne h]
      have hb'c : b' ≤ c := setOpen_le_of_mem_diffSet G hle hemem
      have hkb : numClusters G b ≤ numClusters G b' + 1 := numClusters_setOpen_succ_of_closed G hbe
      have hob : chOpenCount G b' = chOpenCount G b + 1 := openCount_setOpen_of_closed G heG hbe
      have hdiff : diffSet G b' c = (diffSet G b c).erase e := diffSet_setOpen G hemem
      have hcard' : (diffSet G b' c).card = n - 1 := by
        rw [hdiff, Finset.card_erase_of_mem hemem, hcard]
      have hlt : n - 1 < n := by omega
      have hrec := ih (n - 1) hlt b' c hb'c hcard'
      omega


theorem edgeProduct_modular (p : ℝ) (a b : ConfigSpace (Sym2 V)) :
    edgeProduct G p a * edgeProduct G p b
      = edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
  unfold edgeProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hinf : (a ⊓ b) e = (a e && b e) := rfl
  have hsup : (a ⊔ b) e = (a e || b e) := rfl
  rw [hinf, hsup]
  cases a e <;> cases b e <;> · simp; try ring


theorem fkWeight_cross_bernoulli_upper {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    fkWeight G p q a * edgeProduct G p b
      ≤ fkWeight G p q (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
  unfold fkWeight
  have hmod := edgeProduct_modular G p a b
  have hclust : q ^ numClusters G a ≤ q ^ numClusters G (a ⊓ b) :=
    pow_le_pow_right₀ hq (numClusters_antitone G inf_le_left)
  have hep_nonneg : 0 ≤ edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b) :=
    le_of_lt (mul_pos (edgeProduct_pos G hp hp1 _) (edgeProduct_pos G hp hp1 _))
  calc edgeProduct G p a * q ^ numClusters G a * edgeProduct G p b
      = (edgeProduct G p a * edgeProduct G p b) * q ^ numClusters G a := by ring
    _ = (edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b)) * q ^ numClusters G a := by rw [hmod]
    _ ≤ (edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b)) * q ^ numClusters G (a ⊓ b) :=
        mul_le_mul_of_nonneg_left hclust hep_nonneg
    _ = edgeProduct G p (a ⊓ b) * q ^ numClusters G (a ⊓ b) * edgeProduct G p (a ⊔ b) := by ring


end FK
end StatMech
