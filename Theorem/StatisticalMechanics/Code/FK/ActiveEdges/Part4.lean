/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InhomogeneousFKG
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Def.StatisticalMechanics.Code.FK.ActiveEdges.Part4
open scoped BigOperators
open Finset


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


section ClosedProduct

variable {E : Type*} [Fintype E] [DecidableEq E]

lemma closedProd_antitone (S : Finset E) : Antitone (closedProd S) := by
  intro ω η hωη
  unfold closedProd
  apply Finset.prod_le_prod
  · intro e he
    positivity
  · intro e he
    have h := hωη e
    cases hω : ω e <;> cases hη : η e <;>
      simp_all (config := { decide := true })
    have hn : ¬ ((true : Bool) ≤ false) := by decide
    exact False.elim (hn h)

lemma closedProd_insert {e : E} {S : Finset E} (he : e ∉ S)
    (ω : ConfigSpace E) :
    closedProd (insert e S) ω = closedProd S ω * closedProd {e} ω := by
  simp [closedProd, he, mul_comm]

lemma fkg_inequality_antitone {μ : ConfigSpace E → ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ)
    {f g : ConfigSpace E → ℝ} (hf : Antitone f) (hg : Antitone g) :
    (∑ ω, μ ω * f ω) * (∑ ω, μ ω * g ω) ≤
      ∑ ω, μ ω * (f ω * g ω) := by
  have hnf : Monotone (fun ω => -f ω) := by
    intro a b hab
    exact neg_le_neg (hf hab)
  have hng : Monotone (fun ω => -g ω) := by
    intro a b hab
    exact neg_le_neg (hg hab)
  have h := fkg_inequality hμ0 hμ1 hFKG hnf hng
  simpa only [mul_neg, Finset.sum_neg_distrib, neg_mul, neg_neg] using h

lemma mean_closedProd_singleton (μ : ConfigSpace E → ℝ)
    (hμ1 : ∑ ω, μ ω = 1) (e : E) :
    (∑ ω, μ ω * closedProd {e} ω) = 1 - openMarginal μ e := by
  have hopen : openMarginal μ e =
      ∑ ω, μ ω * (if ω e then (1 : ℝ) else 0) := by
    unfold openMarginal
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : ω e = true <;> simp [h]
  rw [hopen]
  unfold closedProd
  simp only [Finset.prod_singleton]
  calc
    (∑ ω, μ ω * if ω e then 0 else 1) =
        ∑ ω, (μ ω - μ ω * if ω e then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro ω _
      cases h : ω e <;> simp [h]
    _ = (∑ ω, μ ω) - ∑ ω, μ ω * (if ω e then 1 else 0) := by
      rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ ω, μ ω * (if ω e then 1 else 0) := by rw [hμ1]


theorem prod_one_sub_openMarginal_le_closedProd
    (μ : ConfigSpace E → ℝ) (hμ0 : 0 ≤ μ) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) (S : Finset E) :
    (∏ e ∈ S, (1 - openMarginal μ e)) ≤
      ∑ ω, μ ω * closedProd S ω := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [closedProd, hμ1]
  | @insert e S he ih =>
      rw [Finset.prod_insert he]
      have hsingle0 : 0 ≤ 1 - openMarginal μ e := by
        rw [← mean_closedProd_singleton μ hμ1 e]
        apply Finset.sum_nonneg
        intro ω _
        apply mul_nonneg (hμ0 ω)
        simp only [closedProd, Finset.prod_singleton]
        split <;> norm_num
      calc
        (1 - openMarginal μ e) * ∏ x ∈ S, (1 - openMarginal μ x)
            ≤ (1 - openMarginal μ e) *
                ∑ ω, μ ω * closedProd S ω :=
          mul_le_mul_of_nonneg_left ih hsingle0
        _ = (∑ ω, μ ω * closedProd S ω) *
              (∑ ω, μ ω * closedProd {e} ω) := by
          rw [mean_closedProd_singleton μ hμ1 e]
          ring
        _ ≤ ∑ ω, μ ω * (closedProd S ω * closedProd {e} ω) :=
          fkg_inequality_antitone hμ0 hμ1 hFKG
            (closedProd_antitone S) (closedProd_antitone {e})
        _ = ∑ ω, μ ω * closedProd (insert e S) ω := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [closedProd_insert he]

end ClosedProduct


theorem active_prod_closed_param_le {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) (S : Finset G.edgeSet) :
    (∏ e ∈ S, (1 - pf e.1)) ≤
      ∑ ω, activeProb G pf q ω * closedProd S ω := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hμ0 : 0 ≤ activeProb G pf q :=
    fun ω => (activeProb_pos G hpf hpf1 hq0 ω).le
  have hμ1 := activeProb_sum_eq_one G hpf hpf1 hq0
  have hFKG := activeProb_FKGLatticeCondition G hpf hpf1 hq
  refine (Finset.prod_le_prod (fun e he => by linarith [hpf1 e.1]) ?_).trans
    (prod_one_sub_openMarginal_le_closedProd _ hμ0 hμ1 hFKG S)
  intro e he
  linarith [active_openMarginal_le_param G hpf hpf1 hq e]

lemma betaScore_extendActive (J : Sym2 V → ℝ) (β : ℝ)
    (ω : ConfigSpace G.edgeSet) :
    betaScore G J β (extendActive G ω) = activeBetaScore G J β ω := by
  unfold betaScore activeBetaScore
  rw [Finset.sum_subtype G.edgeFinset]
  · apply Finset.sum_congr rfl
    intro e _
    congr 2
    simp [coordR, OSSS.Lindeberg.coord, extendActive_apply]
  · intro e
    rw [SimpleGraph.mem_edgeFinset]

theorem hasDerivAt_activeWeight_beta {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β) (q : ℝ)
    (ω : ConfigSpace G.edgeSet) :
    HasDerivAt (fun b => activeWeight G (betaParams J b) q ω)
      (activeWeight G (betaParams J β) q ω * activeBetaScore G J β ω) β := by
  simpa [activeWeight, betaScore_extendActive] using
    hasDerivAt_fkWeightW_beta G hJ hβ q (extendActive G ω)

theorem hasDerivAt_activeNumer_beta {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β) (q : ℝ)
    (f : ConfigSpace G.edgeSet → ℝ) :
    HasDerivAt (fun b => activeNumer G (betaParams J b) q f)
      (activeNumer G (betaParams J β) q (fun ω => f ω * activeBetaScore G J β ω)) β := by
  unfold activeNumer
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun ω _ => (hasDerivAt_activeWeight_beta G hJ hβ q ω).const_mul (f ω))
  refine hsum.congr_deriv ?_
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma activeNumer_one (pf : Sym2 V → ℝ) (q : ℝ) :
    activeNumer G pf q (fun _ => 1) = activeZ G pf q := by
  simp [activeNumer, activeZ]

lemma activeMean_eq_div (pf : Sym2 V → ℝ) (q : ℝ)
    (f : ConfigSpace G.edgeSet → ℝ) :
    activeMean G pf q f = activeNumer G pf q f / activeZ G pf q := by
  unfold activeMean activeNumer activeProb
  rw [show (fun ω => f ω * (activeWeight G pf q ω / activeZ G pf q)) =
      (fun ω => (f ω * activeWeight G pf q ω) / activeZ G pf q) by
    funext ω
    ring]
  rw [← Finset.sum_div]

lemma activeMean_add (pf : Sym2 V → ℝ) (q : ℝ)
    (f g : ConfigSpace G.edgeSet → ℝ) :
    activeMean G pf q (fun ω => f ω + g ω) =
      activeMean G pf q f + activeMean G pf q g := by
  unfold activeMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma activeMean_const_mul (pf : Sym2 V → ℝ) (q c : ℝ)
    (f : ConfigSpace G.edgeSet → ℝ) :
    activeMean G pf q (fun ω => c * f ω) = c * activeMean G pf q f := by
  unfold activeMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma activeMean_sum (pf : Sym2 V → ℝ) (q : ℝ)
    {ι : Type*} [Fintype ι] (g : ι → ConfigSpace G.edgeSet → ℝ) :
    activeMean G pf q (fun ω => ∑ i, g i ω) =
      ∑ i, activeMean G pf q (g i) := by
  classical
  unfold activeMean
  rw [← Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_mul]

lemma activeCov_const_mul_right (pf : Sym2 V → ℝ) (q c : ℝ)
    (f g : ConfigSpace G.edgeSet → ℝ) :
    activeCov G pf q f (fun ω => c * g ω) = c * activeCov G pf q f g := by
  unfold activeCov
  rw [activeMean_const_mul]
  have hprod : (fun ω => f ω * (c * g ω)) = (fun ω => c * (f ω * g ω)) := by
    funext ω
    ring
  rw [hprod, activeMean_const_mul]
  ring

lemma activeCov_sum_right (pf : Sym2 V → ℝ) (q : ℝ)
    (f : ConfigSpace G.edgeSet → ℝ) {ι : Type*} [Fintype ι]
    (g : ι → ConfigSpace G.edgeSet → ℝ) :
    activeCov G pf q f (fun ω => ∑ i, g i ω) =
      ∑ i, activeCov G pf q f (g i) := by
  classical
  unfold activeCov
  rw [show (fun ω => f ω * ∑ i, g i ω) =
      (fun ω => ∑ i, f ω * g i ω) by funext ω; rw [Finset.mul_sum]]
  rw [activeMean_sum, activeMean_sum]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]

lemma activeCov_sub_const {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) (f g : ConfigSpace G.edgeSet → ℝ) (c : ℝ) :
    activeCov G pf q f (fun ω => g ω - c) = activeCov G pf q f g := by
  have hone : activeMean G pf q (fun _ : ConfigSpace G.edgeSet => (1 : ℝ)) = 1 := by
    simpa [activeMean] using activeProb_sum_eq_one G hpf hpf1 hq
  unfold activeCov
  rw [show (fun ω => f ω * (g ω - c)) =
      (fun ω => f ω * g ω + (-c) * f ω) by funext ω; ring]
  rw [activeMean_add, activeMean_const_mul]
  rw [show (fun ω : ConfigSpace G.edgeSet => g ω - c) =
      (fun ω => g ω + (-c) * 1) by funext ω; ring]
  rw [activeMean_add, activeMean_const_mul, hone]
  ring

theorem hasDerivAt_activeMean_beta_sum {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β)
    {q : ℝ} (hq : 0 < q) (f : ConfigSpace G.edgeSet → ℝ) :
    HasDerivAt (fun b => activeMean G (betaParams J b) q f)
      (∑ e : G.edgeSet, (J e.1 / betaParams J β e.1) *
        activeCov G (betaParams J β) q f (OSSS.Lindeberg.coord e)) β := by
  have hN := hasDerivAt_activeNumer_beta G hJ hβ q f
  have hZraw := hasDerivAt_activeNumer_beta G hJ hβ q (fun _ => 1)
  have hZ : HasDerivAt (fun b => activeZ G (betaParams J b) q)
      (activeNumer G (betaParams J β) q (activeBetaScore G J β)) β := by
    simpa only [activeNumer_one, one_mul] using hZraw
  have hZne : activeZ G (betaParams J β) q ≠ 0 :=
    (activeZ_pos G (betaParams_pos hJ hβ) (betaParams_lt_one J β) hq).ne'
  rw [show (fun b => activeMean G (betaParams J b) q f) =
      (fun b => activeNumer G (betaParams J b) q f /
        activeZ G (betaParams J b) q) by
    funext b
    exact activeMean_eq_div G _ _ _]
  refine (hN.div hZ hZne).congr_deriv ?_
  have hscore : activeCov G (betaParams J β) q f (activeBetaScore G J β) =
      ∑ e : G.edgeSet, (J e.1 / betaParams J β e.1) *
        activeCov G (betaParams J β) q f (OSSS.Lindeberg.coord e) := by
    unfold activeBetaScore
    rw [activeCov_sum_right]
    apply Finset.sum_congr rfl
    intro e _
    rw [activeCov_const_mul_right]
    rw [activeCov_sub_const G (betaParams_pos hJ hβ)
      (betaParams_lt_one J β) hq]
  rw [← hscore]
  unfold activeCov
  rw [activeMean_eq_div, activeMean_eq_div, activeMean_eq_div]
  field_simp

theorem hasDerivAt_activeProbOf_beta_sum {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β)
    {q : ℝ} (hq : 0 < q) (A : Set (ConfigSpace G.edgeSet)) :
    HasDerivAt (fun b => activeProbOf G (betaParams J b) q A)
      (∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(β * J e.1)))) *
        activeCov G (betaParams J β) q (A.indicator (fun _ => (1 : ℝ)))
          (OSSS.Lindeberg.coord e)) β := by
  simpa [activeProbOf, betaParams] using
    hasDerivAt_activeMean_beta_sum G hJ hβ hq (A.indicator (fun _ => (1 : ℝ)))

end FK
end StatMech
