/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.RussoDerivativeBeta.Part3
open scoped BigOperators


namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


lemma fkNumerW_one (pf : Sym2 V → ℝ) (q : ℝ) :
    fkNumerW G pf q (fun _ => 1) = fkZW G pf q := by
  unfold fkNumerW fkZW
  exact Finset.sum_congr rfl (fun ω _ => by rw [one_mul])


lemma hasDerivAt_fkNumerW {pf : Sym2 V → ℝ} {e₀ : Sym2 V} {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ)
    (he : e₀ ∈ G.edgeFinset) :
    HasDerivAt (fun t => fkNumerW G (Function.update pf e₀ t) q g)
      ((∑ ω : ConfigSpace (Sym2 V),
        g ω * (fkWeightW G (Function.update pf e₀ t) q ω * (coordR e₀ ω - t)))
          / (t * (1 - t))) t := by
  unfold fkNumerW
  have hsum : HasDerivAt
      (fun t => ∑ ω : ConfigSpace (Sym2 V),
        g ω * fkWeightW G (Function.update pf e₀ t) q ω)
      (∑ ω : ConfigSpace (Sym2 V),
        g ω * (fkWeightW G (Function.update pf e₀ t) q ω
          * ((coordR e₀ ω - t) / (t * (1 - t))))) t := by
    apply HasDerivAt.fun_sum
    intro ω _
    exact (hasDerivAt_fkWeightW (pf := pf) G ht ht1 q ω he).const_mul (g ω)
  refine hsum.congr_deriv ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [mul_div_assoc, mul_div_assoc]


lemma fkMeanW_eq_div (pf : Sym2 V → ℝ) (q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    fkMeanW G pf q g = fkNumerW G pf q g / fkZW G pf q := by
  unfold fkMeanW fkNumerW fkProbW
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [mul_div_assoc]


lemma fkMeanW_add (pf : Sym2 V → ℝ) (q : ℝ) (g h : ConfigSpace (Sym2 V) → ℝ) :
    fkMeanW G pf q (fun ω => g ω + h ω) = fkMeanW G pf q g + fkMeanW G pf q h := by
  unfold fkMeanW
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma fkMeanW_const (pf : Sym2 V → ℝ) (q : ℝ) {c : ℝ}
    (hZ : fkZW G pf q ≠ 0) : fkMeanW G pf q (fun _ => c) = c := by
  unfold fkMeanW fkProbW
  have hstep : ∀ ω : ConfigSpace (Sym2 V), c * (fkWeightW G pf q ω / fkZW G pf q)
      = (c * fkWeightW G pf q ω) / fkZW G pf q := fun ω => by rw [mul_div_assoc]
  rw [Finset.sum_congr rfl (fun ω _ => hstep ω), ← Finset.sum_div, ← Finset.mul_sum]
  show (c * fkZW G pf q) / fkZW G pf q = c
  rw [mul_div_assoc, div_self hZ, mul_one]


lemma fkMeanW_const_mul (pf : Sym2 V → ℝ) (q : ℝ) (c : ℝ)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    fkMeanW G pf q (fun ω => c * g ω) = c * fkMeanW G pf q g := by
  unfold fkMeanW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  ring


lemma fkCovW_sub_const (pf : Sym2 V → ℝ) (q : ℝ)
    (f g : ConfigSpace (Sym2 V) → ℝ) {c : ℝ} (hZ : fkZW G pf q ≠ 0) :
    fkCovW G pf q f (fun ω => g ω - c) = fkCovW G pf q f g := by
  unfold fkCovW
  have hprod : fkMeanW G pf q (fun ω => f ω * (g ω - c))
      = fkMeanW G pf q (fun ω => f ω * g ω) - c * fkMeanW G pf q f := by
    have heq : (fun ω => f ω * (g ω - c)) = (fun ω => f ω * g ω + (-c) * f ω) := by
      funext ω; ring
    rw [heq, fkMeanW_add, fkMeanW_const_mul]
    ring
  have hgc : fkMeanW G pf q (fun ω => g ω - c) = fkMeanW G pf q g - c := by
    have heq : (fun ω => g ω - c) = (fun ω => g ω + (fun _ => -c) ω) := by funext ω; ring
    rw [heq, fkMeanW_add, fkMeanW_const G pf q hZ]; ring
  rw [hprod, hgc]; ring


theorem hasDerivAt_fkMeanW {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) {e₀ : Sym2 V} (he : e₀ ∈ G.edgeFinset)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    HasDerivAt (fun t => fkMeanW G (Function.update pf e₀ t) q g)
      (fkCovW G (Function.update pf e₀ (pf e₀)) q g (coordR e₀) / (pf e₀ * (1 - pf e₀)))
      (pf e₀) := by
  set t₀ := pf e₀ with ht₀
  have ht : 0 < t₀ := hpf e₀
  have ht1 : t₀ < 1 := hpf1 e₀
  have hppos : 0 < t₀ * (1 - t₀) := mul_pos ht (by linarith)
  have hpne : t₀ * (1 - t₀) ≠ 0 := hppos.ne'
  
  have hupd_pos : ∀ s : ℝ, 0 < s → s < 1 → ∀ e, 0 < Function.update pf e₀ s e := by
    intro s hs _ e
    by_cases h : e = e₀
    · subst h; rw [Function.update_self]; exact hs
    · rw [Function.update_of_ne h]; exact hpf e
  have hupd_lt : ∀ s : ℝ, 0 < s → s < 1 → ∀ e, Function.update pf e₀ s e < 1 := by
    intro s hs hs1 e
    by_cases h : e = e₀
    · subst h; rw [Function.update_self]; exact hs1
    · rw [Function.update_of_ne h]; exact hpf1 e
  
  
  have hN : HasDerivAt (fun t => fkNumerW G (Function.update pf e₀ t) q g)
      (fkNumerW G (Function.update pf e₀ t₀) q (fun ω => g ω * (coordR e₀ ω - t₀))
        / (t₀ * (1 - t₀))) t₀ := by
    have h := hasDerivAt_fkNumerW (pf := pf) G ht ht1 q g he
    refine h.congr_deriv ?_
    congr 1
    unfold fkNumerW
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    ring
  have hZd : HasDerivAt (fun t => fkZW G (Function.update pf e₀ t) q)
      (fkNumerW G (Function.update pf e₀ t₀) q (fun ω => coordR e₀ ω - t₀)
        / (t₀ * (1 - t₀))) t₀ := by
    have h := hasDerivAt_fkNumerW (pf := pf) G ht ht1 q (fun _ => 1) he
    have hfun : (fun t => fkNumerW G (Function.update pf e₀ t) q (fun _ => 1))
        = (fun t => fkZW G (Function.update pf e₀ t) q) := by
      funext s; exact fkNumerW_one G (Function.update pf e₀ s) q
    rw [hfun] at h
    refine h.congr_deriv ?_
    congr 1
    unfold fkNumerW
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    ring
  
  have hZne : fkZW G (Function.update pf e₀ t₀) q ≠ 0 :=
    fkZW_ne_zero G (hupd_pos t₀ ht ht1) (hupd_lt t₀ ht ht1) hq
  
  have hdiv := HasDerivAt.div hN hZd hZne
  have hexp : (fun t => fkMeanW G (Function.update pf e₀ t) q g)
      = (fun t => fkNumerW G (Function.update pf e₀ t) q g)
        / (fun t => fkZW G (Function.update pf e₀ t) q) := by
    funext s; rw [fkMeanW_eq_div]; rfl
  rw [hexp]
  refine hdiv.congr_deriv ?_
  
  set Pf := Function.update pf e₀ t₀ with hPf
  set N := fkNumerW G Pf q g with hNdef
  set Z := fkZW G Pf q with hZdef
  set NgC := fkNumerW G Pf q (fun ω => g ω * (coordR e₀ ω - t₀)) with hNgC
  set NC := fkNumerW G Pf q (fun ω => coordR e₀ ω - t₀) with hNC
  
  have hgC : fkMeanW G Pf q (fun ω => g ω * (coordR e₀ ω - t₀)) = NgC / Z :=
    fkMeanW_eq_div G Pf q _
  have hCexp : fkMeanW G Pf q (fun ω => coordR e₀ ω - t₀) = NC / Z :=
    fkMeanW_eq_div G Pf q _
  have hgexp : fkMeanW G Pf q g = N / Z := fkMeanW_eq_div G Pf q g
  
  have hcov : fkCovW G Pf q g (fun ω => coordR e₀ ω - t₀)
      = (NgC * Z - N * NC) / Z ^ 2 := by
    unfold fkCovW
    rw [hgC, hCexp, hgexp]
    field_simp
  
  have hshift : fkCovW G Pf q g (fun ω => coordR e₀ ω - t₀)
      = fkCovW G Pf q g (coordR e₀) :=
    fkCovW_sub_const G Pf q g (coordR e₀) hZne
  
  show (NgC / (t₀ * (1 - t₀)) * Z - N * (NC / (t₀ * (1 - t₀)))) / Z ^ 2
      = fkCovW G Pf q g (coordR e₀) / (t₀ * (1 - t₀))
  rw [← hshift, hcov]
  field_simp


theorem deriv_fkMeanW {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) {e₀ : Sym2 V} (he : e₀ ∈ G.edgeFinset)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    deriv (fun t => fkMeanW G (Function.update pf e₀ t) q g) (pf e₀)
      = fkCovW G (Function.update pf e₀ (pf e₀)) q g (coordR e₀)
        / (pf e₀ * (1 - pf e₀)) :=
  (hasDerivAt_fkMeanW G hpf hpf1 hq he g).deriv


end FK
end StatMech
