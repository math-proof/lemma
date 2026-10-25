/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Def.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace Lindeberg

open OSSS.Monotonic OSSS.Coding

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma delta_nonneg {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hFKG : FKGLatticeCondition μ)
    (F : Finset E) (e : E) {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    (ω : ConfigSpace E) : 0 ≤ delta μ F e f ω := by
  unfold delta
  have := (cExp_mono hpos hFKG (insert e F) hf hf0) (setClosed_le_setOpen e ω)
  linarith


lemma delta_le_one {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (e : E)
    {f : ConfigSpace E → ℝ} (hf1 : ∀ ω, f ω ≤ 1) (hf0 : 0 ≤ f) (ω : ConfigSpace E) :
    delta μ F e f ω ≤ 1 := by
  unfold delta
  have h1 := cExp_le_one hpos (insert e F) hf1 (setOpen e ω)
  have h2 := cExp_nonneg hpos (insert e F) hf0 (setClosed e ω)
  linarith


lemma delta_Fmeas (μ : ConfigSpace E → ℝ) (F : Finset E) (e : E) (he : e ∉ F)
    (f : ConfigSpace E → ℝ) : Fmeas F (delta μ F e f) := by
  intro η η' h
  unfold delta
  have hne : ∀ x ∈ F, x ≠ e := fun x hxF => by rintro rfl; exact he hxF
  congr 1
  · apply cExp_Fmeas μ (insert e F) f
    intro x hx; rcases Finset.mem_insert.mp hx with rfl | hxF
    · rw [setOpen_self, setOpen_self]
    · rw [setOpen_of_ne (hne x hxF), setOpen_of_ne (hne x hxF)]; exact h x hxF
  · apply cExp_Fmeas μ (insert e F) f
    intro x hx; rcases Finset.mem_insert.mp hx with rfl | hxF
    · rw [setClosed_self, setClosed_self]
    · rw [setClosed_of_ne (hne x hxF), setClosed_of_ne (hne x hxF)]; exact h x hxF


lemma cExp_branch (μ : ConfigSpace E → ℝ) (F : Finset E) (e : E)
    (f : ConfigSpace E → ℝ) (ω : ConfigSpace E) :
    cExp μ (insert e F) f ω
      = if ω e then cExp μ (insert e F) f (setOpen e ω) else cExp μ (insert e F) f (setClosed e ω) := by
  by_cases hb : ω e = true
  · rw [if_pos hb]
    apply cExp_Fmeas μ (insert e F) f ω (setOpen e ω)
    intro x _; by_cases hxe : x = e
    · subst hxe; rw [setOpen_self]; exact hb
    · rw [setOpen_of_ne hxe]
  · have hb' : ω e = false := by cases hh : ω e; rfl; exact absurd hh hb
    rw [if_neg hb]
    apply cExp_Fmeas μ (insert e F) f ω (setClosed e ω)
    intro x _; by_cases hxe : x = e
    · subst hxe; rw [setClosed_self]; exact hb'
    · rw [setClosed_of_ne hxe]


lemma step_factor {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (e : E)
    (he : e ∉ F) (f : ConfigSpace E → ℝ) (ω : ConfigSpace E) :
    cExp μ (insert e F) f ω - cExp μ F f ω
      = delta μ F e f ω * (coord e ω - cExp μ F (coord e) ω) := by
  rw [cExp_decomp hpos F e he f ω, cExp_branch μ F e f ω]
  have hcoord : coord e ω = if ω e then (1 : ℝ) else 0 := rfl
  unfold delta
  by_cases hbit : ω e = true
  · rw [if_pos hbit, hcoord, if_pos hbit]; ring
  · have hbit' : ω e = false := by cases hh : ω e; rfl; exact absurd hh hbit
    rw [if_neg hbit, hcoord, if_neg hbit]; ring


lemma step_le_cov {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) (F : Finset E) (e : E) (he : e ∉ F)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    mean μ (fun ω => (cExp μ (insert e F) f ω - cExp μ F f ω) ^ 2) ≤ cov μ f (coord e) := by
  set D := fun ω => cExp μ (insert e F) f ω - cExp μ F f ω with hD
  set δ := delta μ F e f with hδ
  set N := cExp μ F (coord e) with hNdef
  have hDfac : ∀ ω, D ω = δ ω * (coord e ω - N ω) := by
    intro ω; rw [hD]; simp only []; rw [step_factor hpos F e he f ω]
  
  have hstepA : mean μ (fun ω => (D ω) ^ 2) ≤ mean μ (fun ω => D ω * coord e ω) := by
    
    have hzero : (∑ ω, (δ ω * N ω * (coord e ω - N ω)) * μ ω) = 0 := by
      have hFm : Fmeas F (fun ω => δ ω * N ω) := by
        intro η η' h
        have h1 := delta_Fmeas μ F e he f η η' h
        have h2 := cExp_Fmeas μ F (coord e) η η' h
        show δ η * N η = δ η' * N η'
        rw [hδ, hNdef, h1, h2]
      have hpull := cExp_pullout hpos F (coord e) (fun ω => δ ω * N ω) hFm
      have hpull' : (∑ ω, ((N ω) * (δ ω * N ω)) * μ ω) = ∑ ω, (coord e ω * (δ ω * N ω)) * μ ω :=
        hpull
      have hexp : (∑ ω, (δ ω * N ω * (coord e ω - N ω)) * μ ω)
          = (∑ ω, (coord e ω * (δ ω * N ω)) * μ ω) - (∑ ω, ((N ω) * (δ ω * N ω)) * μ ω) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun ω _ => by ring)
      rw [hexp, hpull']; ring
    have hdiff : mean μ (fun ω => D ω * coord e ω) - mean μ (fun ω => (D ω) ^ 2)
        = ∑ ω, (δ ω * (1 - δ ω) * (coord e ω - N ω) ^ 2) * μ ω := by
      unfold mean
      rw [← Finset.sum_sub_distrib]
      have expand : ∀ ω, (D ω * coord e ω) * μ ω - ((D ω) ^ 2) * μ ω
          = (δ ω * (1 - δ ω) * (coord e ω - N ω) ^ 2) * μ ω
            + (δ ω * N ω * (coord e ω - N ω)) * μ ω := by
        intro ω; rw [hDfac ω]; ring
      simp_rw [expand]
      rw [Finset.sum_add_distrib, hzero, add_zero]
    have hge : 0 ≤ ∑ ω, (δ ω * (1 - δ ω) * (coord e ω - N ω) ^ 2) * μ ω := by
      apply Finset.sum_nonneg; intro ω _
      refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) (hpos ω).le
      · exact delta_nonneg hpos hFKG F e hf hf0 ω
      · have := delta_le_one hpos F e hf1 hf0 ω; rw [hδ]; linarith
      · positivity
    linarith [hdiff, hge]
  
  have hstepB : mean μ (fun ω => D ω * coord e ω) ≤ cov μ f (coord e) := by
    have hcoordFmeas : Fmeas (insert e F) (coord e) := by
      intro η η' h; unfold coord; rw [h e (Finset.mem_insert_self e F)]
    have h1 : mean μ (fun ω => cExp μ (insert e F) f ω * coord e ω)
        = mean μ (fun ω => f ω * coord e ω) := by
      unfold mean; exact cExp_pullout hpos (insert e F) f (coord e) hcoordFmeas
    have hcExpFf_Fmeas : Fmeas F (cExp μ F f) := cExp_Fmeas μ F f
    have h2 : mean μ (fun ω => cExp μ F f ω * coord e ω)
        = mean μ (fun ω => cExp μ F f ω * N ω) := by
      have hp := cExp_pullout hpos F (coord e) (cExp μ F f) hcExpFf_Fmeas
      unfold mean
      rw [show (fun ω => cExp μ F f ω * coord e ω) = (fun ω => coord e ω * cExp μ F f ω) from by
            funext ω; ring]
      rw [show (∑ ω, (fun ω => coord e ω * cExp μ F f ω) ω * μ ω)
            = ∑ ω, (coord e ω * cExp μ F f ω) * μ ω from rfl, ← hp]
      exact Finset.sum_congr rfl (fun ω _ => by rw [hNdef]; ring)
    have hDexp : mean μ (fun ω => D ω * coord e ω)
        = mean μ (fun ω => f ω * coord e ω) - mean μ (fun ω => cExp μ F f ω * N ω) := by
      have hsub : mean μ (fun ω => D ω * coord e ω)
          = mean μ (fun ω => cExp μ (insert e F) f ω * coord e ω)
            - mean μ (fun ω => cExp μ F f ω * coord e ω) := by
        unfold mean
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun ω _ => by rw [hD]; simp only []; ring)
      rw [hsub, h1, h2]
    rw [hDexp]
    have hmono1 : Monotone (cExp μ F f) := cExp_mono hpos hFKG F hf hf0
    have hmono2 : Monotone N := by
      rw [hNdef]; exact cExp_mono hpos hFKG F (coord_mono e) (coord_nonneg e)
    have hfkg := mean_mul_ge hpos hμ1 hFKG hmono1 hmono2
    rw [mean_cExp hpos F f, hNdef, mean_cExp hpos F (coord e), ← hNdef] at hfkg
    unfold cov
    linarith [hfkg]
  exact hstepA.trans hstepB


lemma Fmeas_mono {F F' : Finset E} (hsub : F ⊆ F') {h : ConfigSpace E → ℝ} (hh : Fmeas F h) :
    Fmeas F' h := fun η η' heq => hh η η' (fun x hx => heq x (hsub hx))


lemma cExp_univ {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (f : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) : cExp μ Finset.univ f ω = f ω := by
  unfold cExp condMass
  rw [Finset.sum_eq_single ω]
  · rw [condNorm_univ, if_pos (agree_self _ _)]; field_simp [(hpos ω).ne']
  · intro ω' _ hne
    rw [if_neg, zero_div, mul_zero]
    intro hag; exact hne (funext fun x => (hag x (Finset.mem_univ x)))
  · intro h; exact absurd (Finset.mem_univ ω) h


lemma cExp_empty {μ : ConfigSpace E → ℝ} (hμ1 : ∑ ω, μ ω = 1) (f : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) : cExp μ ∅ f ω = mean μ f := by
  unfold cExp condMass mean
  rw [condNorm_empty, hμ1]
  apply Finset.sum_congr rfl; intro ω' _
  rw [if_pos]
  · field_simp
  · intro x hx; exact absurd hx (Finset.notMem_empty x)


lemma projection {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) {F F' : Finset E} (hsub : F ⊆ F')
    (f : ConfigSpace E → ℝ) :
    mean μ (fun ω => cExp μ F' f ω * cExp μ F f ω)
      = mean μ (fun ω => cExp μ F f ω * cExp μ F f ω) := by
  have hFmeas : Fmeas F' (cExp μ F f) := Fmeas_mono hsub (cExp_Fmeas μ F f)
  have h1 : mean μ (fun ω => cExp μ F' f ω * cExp μ F f ω) = mean μ (fun ω => f ω * cExp μ F f ω) := by
    unfold mean; exact cExp_pullout hpos F' f (cExp μ F f) hFmeas
  have h2 : mean μ (fun ω => cExp μ F f ω * cExp μ F f ω) = mean μ (fun ω => f ω * cExp μ F f ω) := by
    unfold mean; exact cExp_pullout hpos F f (cExp μ F f) (cExp_Fmeas μ F f)
  rw [h1, h2]


lemma pythagoras {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) {F F' : Finset E} (hsub : F ⊆ F')
    (f : ConfigSpace E → ℝ) :
    mean μ (fun ω => (cExp μ F' f ω - cExp μ F f ω) ^ 2)
      = mean μ (fun ω => cExp μ F' f ω * cExp μ F' f ω)
        - mean μ (fun ω => cExp μ F f ω * cExp μ F f ω) := by
  have hexpand : mean μ (fun ω => (cExp μ F' f ω - cExp μ F f ω) ^ 2)
      = mean μ (fun ω => cExp μ F' f ω * cExp μ F' f ω)
        - 2 * mean μ (fun ω => cExp μ F' f ω * cExp μ F f ω)
        + mean μ (fun ω => cExp μ F f ω * cExp μ F f ω) := by
    unfold mean
    rw [show (∑ ω, ((cExp μ F' f ω - cExp μ F f ω) ^ 2) * μ ω)
          = ∑ ω, ((cExp μ F' f ω * cExp μ F' f ω) * μ ω
              - 2 * ((cExp μ F' f ω * cExp μ F f ω) * μ ω)
              + (cExp μ F f ω * cExp μ F f ω) * μ ω) from by
          apply Finset.sum_congr rfl; intro ω _; ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexpand, projection hpos hsub f]; ring


lemma var_telescope {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    var μ f = ∑ t ∈ Finset.range n,
      mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) (t + 1)) f ω
                          - cExp μ (prefixSet (σ : Fin n → E) t) f ω) ^ 2) := by
  set g : ℕ → ℝ := fun t =>
    mean μ (fun ω => cExp μ (prefixSet (σ : Fin n → E) t) f ω
                      * cExp μ (prefixSet (σ : Fin n → E) t) f ω) with hg
  have hterm : ∀ t ∈ Finset.range n,
      mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) (t + 1)) f ω
                          - cExp μ (prefixSet (σ : Fin n → E) t) f ω) ^ 2) = g (t + 1) - g t := by
    intro t ht
    rw [Finset.mem_range] at ht
    have hsub : prefixSet (σ : Fin n → E) t ⊆ prefixSet (σ : Fin n → E) (t + 1) := by
      rw [prefixSet_succ_lt (σ : Fin n → E) t ht]; exact Finset.subset_insert _ _
    rw [pythagoras hpos hsub f]
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub g n]
  have hgn : g n = mean μ (fun ω => f ω * f ω) := by
    show mean μ (fun ω => cExp μ (prefixSet (σ : Fin n → E) n) f ω
                          * cExp μ (prefixSet (σ : Fin n → E) n) f ω) = _
    rw [prefixSet_card σ]
    unfold mean; apply Finset.sum_congr rfl; intro ω _
    simp only [cExp_univ hpos f ω]
  have hg0 : g 0 = mean μ f * mean μ f := by
    show mean μ (fun ω => cExp μ (prefixSet (σ : Fin n → E) 0) f ω
                          * cExp μ (prefixSet (σ : Fin n → E) 0) f ω) = _
    rw [prefixSet_zero]
    unfold mean
    have hc : (fun ω => cExp μ ∅ f ω * cExp μ ∅ f ω) = (fun _ => mean μ f * mean μ f) := by
      funext ω; rw [cExp_empty hμ1 f ω]
    rw [hc]
    simp only []
    rw [← Finset.mul_sum, hμ1, mul_one]
    rfl
  rw [hgn, hg0]
  unfold var cov; ring


theorem monotonic_poincare {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    var μ f ≤ ∑ e, cov μ f (coord e) := by
  classical
  
  set n := Fintype.card E with hn
  set σ : Fin n ≃ E := (Fintype.equivFin E).symm with hσ
  rw [var_telescope hpos hμ1 σ f]
  
  have hreindex : ∑ t ∈ Finset.range n,
      mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) (t + 1)) f ω
                          - cExp μ (prefixSet (σ : Fin n → E) t) f ω) ^ 2)
      = ∑ i : Fin n,
          mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) ((i : ℕ) + 1)) f ω
                            - cExp μ (prefixSet (σ : Fin n → E) (i : ℕ)) f ω) ^ 2) := by
    rw [Finset.sum_range fun t =>
      mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) (t + 1)) f ω
                          - cExp μ (prefixSet (σ : Fin n → E) t) f ω) ^ 2)]
  rw [hreindex]
  
  have hbound : ∀ i : Fin n,
      mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) ((i : ℕ) + 1)) f ω
                          - cExp μ (prefixSet (σ : Fin n → E) (i : ℕ)) f ω) ^ 2)
        ≤ cov μ f (coord ((σ : Fin n → E) i)) := by
    intro i
    rw [prefixSet_succ_lt (σ : Fin n → E) (i : ℕ) i.2]
    have hi : (⟨(i : ℕ), i.2⟩ : Fin n) = i := rfl
    rw [hi]
    have hnotmem : (σ : Fin n → E) i ∉ prefixSet (σ : Fin n → E) (i : ℕ) := by
      rw [mem_prefixSet_iff]
      rintro ⟨s, hs, hseq⟩
      have := σ.injective hseq
      rw [this] at hs; exact (lt_irrefl (i : ℕ)) hs
    exact step_le_cov hpos hμ1 hFKG _ _ hnotmem hf hf0 hf1
  calc ∑ i : Fin n,
        mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) ((i : ℕ) + 1)) f ω
                            - cExp μ (prefixSet (σ : Fin n → E) (i : ℕ)) f ω) ^ 2)
      ≤ ∑ i : Fin n, cov μ f (coord ((σ : Fin n → E) i)) := Finset.sum_le_sum (fun i _ => hbound i)
    _ = ∑ e, cov μ f (coord e) := Equiv.sum_comp σ (fun e => cov μ f (coord e))


open OSSS.MonotonicMeasure in

lemma cov_eq_genCov (μ : ConfigSpace E → ℝ) (f g : ConfigSpace E → ℝ) :
    cov μ f g = genCov μ f g := rfl

open OSSS.MonotonicMeasure in

lemma var_eq_genVar (μ : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) :
    var μ g = genVar μ g := rfl

open OSSS.MonotonicMeasure in

lemma coord_eq_genCoord (e : E) : (coord e : ConfigSpace E → ℝ) = genCoord e := rfl

open OSSS.MonotonicMeasure in


theorem monotonicOSSSBound_poincare {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    MonotonicOSSSBound μ Finset.univ f 1 1 1 := by
  unfold MonotonicOSSSBound
  rw [← var_eq_genVar]
  have hmain := monotonic_poincare hpos hμ1 hFKG hf hf0 hf1
  
  rw [Nat.cast_one, one_mul, one_mul, one_mul]
  refine hmain.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro e _
  rw [← cov_eq_genCov, ← coord_eq_genCoord]
  
  unfold cov mean
  rw [show (fun ω => f ω * coord e ω) = (fun ω => coord e ω * f ω) from by funext ω; ring]
  ring


open MonotonicFK OSSS.MonotonicMeasure in


theorem fk_monotonic_poincare {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) {f : ConfigSpace (Sym2 V) → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    var (fkMass G p q) f ≤ ∑ e, cov (fkMass G p q) f (coord e) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact monotonic_poincare
    (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_sum_eq_one G hp hp1 hq0)
    (FK.fkProb_FKGLatticeCondition G hp hp1 hq) hf hf0 hf1

open MonotonicFK OSSS.MonotonicMeasure in


theorem fk_monotonicOSSSBound_poincare {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) {f : ConfigSpace (Sym2 V) → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    MonotonicOSSSBound (fkMass G p q) Finset.univ f 1 1 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact monotonicOSSSBound_poincare
    (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_sum_eq_one G hp hp1 hq0)
    (FK.fkProb_FKGLatticeCondition G hp hp1 hq) hf hf0 hf1

end Lindeberg
end OSSS
end StatMech
