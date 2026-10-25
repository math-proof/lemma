/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcNontrivial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
open MeasureTheory Filter Topology Set SimpleGraph
open scoped NNReal ENNReal BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


theorem openGraph_mono {a b : ConfigSpace (Sym2 V)} (h : a ≤ b) :
    openGraph G a ≤ openGraph G b := by
  intro x y hxy
  rw [openGraph_adj] at hxy ⊢
  refine ⟨hxy.1, ?_⟩
  have := h s(x, y)
  rw [hxy.2] at this
  exact le_antisymm le_top this


theorem wiredGraph_mono {a b : ConfigSpace (Sym2 V)} (h : a ≤ b) :
    wiredGraph G bdry a ≤ wiredGraph G bdry b := by
  unfold wiredGraph
  exact sup_le_sup_right (openGraph_mono G h) _


theorem numClustersWired_antitone {a b : ConfigSpace (Sym2 V)} (h : a ≤ b) :
    numClustersWired G bdry b ≤ numClustersWired G bdry a := by
  unfold numClustersWired
  exact SimpleGraph.ConnectedComponent.card_le_card_of_le (wiredGraph_mono G bdry h)


theorem wiredFkWeight_edgeProduct_cross {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    wiredFkWeight G bdry p q a * edgeProduct G p b
      ≤ wiredFkWeight G bdry p q (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
  unfold wiredFkWeight
  
  have hmod : edgeProduct G p a * edgeProduct G p b
      = edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
    rw [edgeProduct_logModular G p a b]; ring
  
  have hk : numClustersWired G bdry a ≤ numClustersWired G bdry (a ⊓ b) :=
    numClustersWired_antitone G bdry inf_le_left
  have hclust : q ^ numClustersWired G bdry a ≤ q ^ numClustersWired G bdry (a ⊓ b) :=
    pow_le_pow_right₀ hq hk
  
  have hepa : (0 : ℝ) ≤ edgeProduct G p a := (edgeProduct_pos G hp hp1 a).le
  have hepb : (0 : ℝ) ≤ edgeProduct G p b := (edgeProduct_pos G hp hp1 b).le
  have hepab : (0 : ℝ) ≤ edgeProduct G p (a ⊓ b) := (edgeProduct_pos G hp hp1 (a ⊓ b)).le
  have hepsup : (0 : ℝ) ≤ edgeProduct G p (a ⊔ b) := (edgeProduct_pos G hp hp1 (a ⊔ b)).le
  have hqa : (0 : ℝ) ≤ q ^ numClustersWired G bdry a := pow_nonneg (by linarith) _
  
  calc edgeProduct G p a * q ^ numClustersWired G bdry a * edgeProduct G p b
      = (edgeProduct G p a * edgeProduct G p b) * q ^ numClustersWired G bdry a := by ring
    _ = (edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b)) * q ^ numClustersWired G bdry a := by
          rw [hmod]
    _ ≤ (edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b)) * q ^ numClustersWired G bdry (a ⊓ b) := by
          apply mul_le_mul_of_nonneg_left hclust
          exact mul_nonneg hepab hepsup
    _ = edgeProduct G p (a ⊓ b) * q ^ numClustersWired G bdry (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
          ring


theorem wiredFkProb_fkProbOne_cross {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    wiredFkProb G bdry p q a * fkProb G p 1 b
      ≤ wiredFkProb G bdry p q (a ⊓ b) * fkProb G p 1 (a ⊔ b) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hZ1 : 0 < wiredFkZ G bdry p q := wiredFkZ_pos G bdry hp hp1 hq0
  have hZ2 : 0 < fkZ G p 1 := fkZ_pos G hp hp1 one_pos
  unfold wiredFkProb fkProb
  rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2)]
  rw [fkWeight_one, fkWeight_one]
  exact wiredFkWeight_edgeProduct_cross G bdry hp hp1 hq a b


theorem wiredFkProb_le_fkProbOne_increasing {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb G bdry p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb G p 1 ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun ω => wiredFkProb_nonneg G bdry hp hp1 hq0 ω
  · exact fun ω => fkProb_nonneg G hp hp1 one_pos ω
  · rw [wiredFkProb_sum_eq_one G bdry hp hp1 hq0, fkProb_sum_eq_one G hp hp1 one_pos]
  · exact fun a b => wiredFkProb_fkProbOne_cross G bdry hp hp1 hq a b


theorem sum_prod_factor {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι)
    (h : ι → Bool → ℝ) :
    ∑ ω : ι → Bool, ∏ e ∈ s, h e (ω e)
      = 2 ^ (Fintype.card ι - s.card) * ∏ e ∈ s, (∑ b : Bool, h e b) := by
  classical
  set hbar : ι → Bool → ℝ := fun e b => if e ∈ s then h e b else 1 with hhbar
  have key : ∀ ω : ι → Bool, ∏ e ∈ s, h e (ω e) = ∏ e : ι, hbar e (ω e) := by
    intro ω; rw [Finset.prod_ite_mem Finset.univ s]; congr 1; ext x; simp
  simp_rw [key]; rw [← Fintype.prod_sum]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ s) (fun e => ∑ b : Bool, hbar e b)]
  have h1 : (Finset.univ.filter (· ∈ s)) = s := by ext x; simp
  have h2 : ∀ e ∈ (Finset.univ.filter (fun e => ¬ e ∈ s)), (∑ b : Bool, hbar e b) = 2 := by
    intro e he; simp only [Finset.mem_filter] at he; simp only [hhbar, if_neg he.2]; simp
  rw [Finset.prod_congr rfl h2, Finset.prod_const]
  have hcard : (Finset.univ.filter (fun e => ¬ e ∈ s)).card = Fintype.card ι - s.card := by
    rw [Finset.filter_not, Finset.card_univ_diff]; simp
  rw [hcard, h1]
  have h3 : ∀ e ∈ s, (∑ b : Bool, hbar e b) = ∑ b : Bool, h e b := by
    intro e he; simp only [hhbar, if_pos he]
  rw [Finset.prod_congr rfl h3]; ring


theorem fkProbOne_cylinder {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (F : Finset (Sym2 V))
    (hF : F ⊆ G.edgeFinset) :
    ∑ ω : ConfigSpace (Sym2 V),
        (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * fkProb G p 1 ω = p ^ F.card := by
  classical
  have hZpos : 0 < fkZ G p 1 := fkZ_pos G hp hp1 one_pos
  have hnum : ∑ ω : ConfigSpace (Sym2 V),
      (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * fkProb G p 1 ω
      = (∑ ω : ConfigSpace (Sym2 V),
          (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * edgeProduct G p ω) / fkZ G p 1 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    unfold fkProb; rw [fkWeight_one]; ring
  rw [hnum]
  set h : Sym2 V → Bool → ℝ :=
    fun e b => if e ∈ F then (if b then p else 0) else (if b then p else 1 - p) with hh
  have hforced : (∑ ω : ConfigSpace (Sym2 V),
      (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * edgeProduct G p ω)
      = ∑ ω : ConfigSpace (Sym2 V), ∏ e ∈ G.edgeFinset, h e (ω e) := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    unfold edgeProduct
    by_cases hall : ∀ e ∈ F, ω e = true
    · rw [if_pos hall, one_mul]
      refine Finset.prod_congr rfl (fun e he => ?_)
      simp only [hh]
      by_cases heF : e ∈ F
      · rw [if_pos heF, hall e heF]; simp
      · rw [if_neg heF]
    · rw [if_neg hall, zero_mul]
      symm
      push Not at hall
      obtain ⟨e0, he0F, he0⟩ := hall
      apply Finset.prod_eq_zero (i := e0) (hF he0F)
      have he0' : ω e0 = false := by simpa using he0
      simp only [hh, if_pos he0F, he0']; simp
  rw [hforced, sum_prod_factor]
  have hZ : fkZ G p 1
      = 2 ^ (Fintype.card (Sym2 V) - G.edgeFinset.card)
        * ∏ e ∈ G.edgeFinset, (∑ b : Bool, (if b then p else 1 - p)) := by
    rw [fkZ_one]
    have heq : (∑ ω : ConfigSpace (Sym2 V), edgeProduct G p ω)
        = ∑ ω : ConfigSpace (Sym2 V),
            ∏ e ∈ G.edgeFinset, (fun (e : Sym2 V) (b : Bool) => if b then p else 1 - p) e (ω e) :=
      rfl
    rw [heq, sum_prod_factor G.edgeFinset (fun (e : Sym2 V) (b : Bool) => if b then p else 1 - p)]
  rw [hZ]
  have hprodF : (∏ e ∈ G.edgeFinset, (∑ b : Bool, h e b))
      = ∏ e ∈ G.edgeFinset, (if e ∈ F then p else 1) := by
    refine Finset.prod_congr rfl (fun e _ => ?_)
    simp only [hh]
    by_cases heF : e ∈ F
    · simp [heF]
    · simp only [heF, if_false]; norm_num
  have hprodZ : (∏ e ∈ G.edgeFinset, (∑ b : Bool, (if b then p else 1 - p)))
      = ∏ e ∈ G.edgeFinset, (1 : ℝ) := by
    refine Finset.prod_congr rfl (fun e _ => ?_); norm_num
  rw [hprodF, hprodZ, Finset.prod_const_one]
  have hpF : (∏ e ∈ G.edgeFinset, (if e ∈ F then p else 1)) = p ^ F.card := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hF, Finset.prod_const]
  rw [hpF]; field_simp


end FK
end StatMech
