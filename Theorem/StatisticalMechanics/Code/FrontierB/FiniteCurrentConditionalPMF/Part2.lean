/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem parityCurrentPMF_apply (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) (m : EdgeCurrent G) :
    parityCurrentPMF G beta hbeta H m =
      ENNReal.ofReal (parityCurrentKernel G beta H m) := by
  rw [parityCurrentPMF, PMF.normalize_apply,
    tsum_ofReal_parityCurrentKernel G beta hbeta H]
  simp

theorem parityCurrentKernel_eq_zero_of_support_ne
    (beta : ℝ) (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset)
    (m : EdgeCurrent G) (hm : currentParitySupport G m ≠ H) :
    parityCurrentKernel G beta H m = 0 := by
  have hall : ¬ ∀ e : G.edgeFinset,
      if e.1 ∈ H then Odd (m e) else Even (m e) :=
    fun h => hm ((currentParitySupport_eq_iff G H hH m).mpr h)
  push Not at hall
  obtain ⟨e, he⟩ := hall
  unfold parityCurrentKernel
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  by_cases heH : e.1 ∈ H
  · have hnot : ¬ Odd (m e) := by simpa [heH] using he
    simp [parityEdgeKernel, heH, hnot]
  · have hnot : ¬ Even (m e) := by simpa [heH] using he
    simp [parityEdgeKernel, heH, hnot]

theorem sourcelessCurrentPMF_apply_eq_parity_factor
    (beta : ℝ) (hbeta : 0 < beta) (m : EdgeCurrent G) :
    sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) m =
      freeParityPMF G beta hbeta.le (currentParitySupport G m) *
        parityCurrentPMF G beta hbeta (currentParitySupport G m) m := by
  let H := currentParitySupport G m
  have hH : H ⊆ G.edgeFinset := currentParitySupport_subset G m
  rw [freeParityPMF_apply, parityCurrentPMF_apply]
  simp only [sourcelessCurrentPMF]
  rw [currentPMF_apply]
  by_cases hsrc : sources G (ofEdgeFun G m) = ∅
  · have heven : IsEvenSubgraph H :=
      (sources_empty_iff_currentParitySupport_even G m).1 hsrc
    have hkernel : 0 ≤ parityCurrentKernel G beta H m := by
      unfold parityCurrentKernel
      exact Finset.prod_nonneg fun e _ =>
        parityEdgeKernel_nonneg beta hbeta (e.1 ∈ H) (m e)
    have htanh : 0 ≤ Real.tanh beta ^ H.card :=
      pow_nonneg (tanh_nonneg_of_nonneg hbeta.le) _
    have hcosh : 0 ≤ Real.cosh beta ^ G.edgeFinset.card := by positivity
    have hw : ENNReal.ofReal
          (weight G beta (fun _ => 1) (ofEdgeFun G m)) =
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) *
          ENNReal.ofReal (Real.tanh beta ^ H.card) *
            ENNReal.ofReal (parityCurrentKernel G beta H m) := by
      rw [weight_eq_parityFiberMass_mul_kernel G beta hbeta H hH m rfl,
        parityFiberMass_closed G beta hbeta.le H hH,
        ENNReal.ofReal_mul (mul_nonneg hcosh htanh),
        ENNReal.ofReal_mul hcosh]
    have hZ : ENNReal.ofReal (currentSum G beta (fun _ => 1) ∅) =
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) *
          ENNReal.ofReal (freeParityPartition G beta) := by
      rw [currentSum_unit_eq_parityPartition G beta,
        ENNReal.ofReal_mul hcosh]
    let c : ℝ≥0∞ := ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card)
    let t : ℝ≥0∞ := ENNReal.ofReal (Real.tanh beta ^ H.card)
    let p : ℝ≥0∞ := ENNReal.ofReal (freeParityPartition G beta)
    let k : ℝ≥0∞ := ENNReal.ofReal (parityCurrentKernel G beta H m)
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
    simp only [currentRawMass, hsrc, if_true, freeParityRawMass,
      hH, heven, and_self, H]
    rw [hw, hZ]
    change c * t * k * (c * p)⁻¹ = t * p⁻¹ * k
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hcTop)]
    calc
      c * t * k * (c⁻¹ * p⁻¹) = (c * c⁻¹) * (t * p⁻¹ * k) := by
        ac_rfl
      _ = t * p⁻¹ * k := by rw [ENNReal.mul_inv_cancel hc0 hcTop, one_mul]
  · have hneven : ¬ IsEvenSubgraph H := by
      intro heven
      exact hsrc ((sources_empty_iff_currentParitySupport_even G m).2 heven)
    have hcond : ¬ (currentParitySupport G m ⊆ G.edgeFinset ∧
        IsEvenSubgraph (currentParitySupport G m)) := by
      intro h
      exact hneven (by simpa [H] using h.2)
    simp [currentRawMass, hsrc, freeParityRawMass, hcond]

theorem sourcelessCurrentPMF_eq_parity_bind
    (beta : ℝ) (hbeta : 0 < beta) :
    sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) =
      (freeParityPMF G beta hbeta.le).bind
        (parityCurrentPMF G beta hbeta) := by
  apply PMF.ext
  intro m
  rw [PMF.bind_apply,
    sourcelessCurrentPMF_apply_eq_parity_factor G beta hbeta m]
  symm
  rw [tsum_eq_single (currentParitySupport G m)]
  intro H hne
  by_cases hH : H ⊆ G.edgeFinset
  · have hk : parityCurrentKernel G beta H m = 0 :=
      parityCurrentKernel_eq_zero_of_support_ne G beta H hH m (Ne.symm hne)
    rw [parityCurrentPMF_apply]
    simp [hk]
  · rw [freeParityPMF_apply]
    simp [freeParityRawMass, hH]

theorem sourcelessCurrentPMF_map_eq_parity_bind
    {A : Type*} (beta : ℝ) (hbeta : 0 < beta)
    (f : EdgeCurrent G → A) :
    PMF.map f (sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one)) =
      (freeParityPMF G beta hbeta.le).bind
        (fun H => PMF.map f (parityCurrentPMF G beta hbeta H)) := by
  rw [sourcelessCurrentPMF_eq_parity_bind G beta hbeta, PMF.map_bind]

theorem sourcelessCurrentFiniteMarginal_eq_parity_bind
    (beta : ℝ) (hbeta : 0 < beta) (S : Finset G.edgeFinset) :
    PMF.map (restrictCurrent S)
        (sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
          (fun _ => zero_le_one)) =
      (freeParityPMF G beta hbeta.le).bind
        (fun H => PMF.map (restrictCurrent S)
          (parityCurrentPMF G beta hbeta H)) :=
  sourcelessCurrentPMF_map_eq_parity_bind G beta hbeta (restrictCurrent S)

end StatMech.FrontierB
