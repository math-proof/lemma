/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.GrandCouplingAssembly.Part6
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
open scoped BigOperators
open MeasureTheory

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace OSSS

namespace AdaptiveCodingLaw

open Coding GrandCoupling GrandCouplingAssembly Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma adaptiveCode_eq_of_mem (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (u : Fin n → ℝ) (x : ConfigSpace E) (hx : u ∈ adaptiveFibre μ σ x) :
    adaptiveCode μ σ u = x := by
  unfold adaptiveCode
  rw [dif_pos ⟨x, hx⟩]
  let y := Classical.choose (show ∃ y, u ∈ adaptiveFibre μ σ y from ⟨x, hx⟩)
  have hy : u ∈ adaptiveFibre μ σ y :=
    Classical.choose_spec (show ∃ y, u ∈ adaptiveFibre μ σ y from ⟨x, hx⟩)
  exact codeMap_eq_unique_of_predictable μ σ hσ u hy hx

lemma measurableSet_adaptiveFibre_union (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) :
    MeasurableSet (⋃ x, adaptiveFibre μ σ x) := by
  exact MeasurableSet.iUnion (fun x => measurableSet_adaptiveFibre μ σ x)


theorem ae_mem_adaptiveFibre_union (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ) :
    ∀ᵐ u ∂(Vcube n), u ∈ ⋃ x, adaptiveFibre μ σ x := by
  refine (ae_iff_measure_eq
    (measurableSet_adaptiveFibre_union μ σ).nullMeasurableSet).2 ?_
  have hreal := predictable_adaptive_fibres_full_measure μ hpos hμ1 σ hσ
  have hmass : (Vcube n) (⋃ x, adaptiveFibre μ σ x) = 1 :=
    (ENNReal.toReal_eq_one_iff _).mp hreal
  simpa using hmass


theorem adaptiveCode_eq_iff_ae (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (x : ConfigSpace E) :
    ∀ᵐ u ∂(Vcube n), adaptiveCode μ σ u = x ↔ u ∈ adaptiveFibre μ σ x := by
  filter_upwards [ae_mem_adaptiveFibre_union μ hpos hμ1 σ hσ] with u hu
  constructor
  · intro hcode
    simp only [Set.mem_iUnion] at hu
    obtain ⟨y, hy⟩ := hu
    have hcy := adaptiveCode_eq_of_mem μ σ hσ u y hy
    have hyx : y = x := hcy.symm.trans hcode
    simpa [hyx] using hy
  · exact adaptiveCode_eq_of_mem μ σ hσ u x


theorem codeMap_selectedOrder_eq_adaptiveCode_ae (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ) :
    ∀ᵐ u ∂(Vcube n),
      codeMap μ (σ (adaptiveCode μ σ u) : Fin n → E) u = adaptiveCode μ σ u := by
  filter_upwards [ae_mem_adaptiveFibre_union μ hpos hμ1 σ hσ] with u hu
  simp only [Set.mem_iUnion] at hu
  obtain ⟨x, hx⟩ := hu
  have hcode := adaptiveCode_eq_of_mem μ σ hσ u x hx
  rw [hcode]
  exact hx


theorem adaptiveCode_fibre_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (x : ConfigSpace E) :
    ((Vcube n) {u | adaptiveCode μ σ u = x}).toReal = μ x := by
  have hset : {u | adaptiveCode μ σ u = x} =ᵐ[Vcube n] adaptiveFibre μ σ x := by
    filter_upwards [adaptiveCode_eq_iff_ae μ hpos hμ1 σ hσ x] with u hu
    exact propext hu
  rw [measure_congr hset]
  exact vcube_adaptiveFibre μ hpos hμ1 σ x


lemma observable_adaptiveCode_ae (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (g : ConfigSpace E → ℝ) :
    (fun u => g (adaptiveCode μ σ u)) =ᵐ[Vcube n]
      (fun u => ∑ x, g x *
        Set.indicator (adaptiveFibre μ σ x) (fun _ => (1 : ℝ)) u) := by
  filter_upwards [ae_mem_adaptiveFibre_union μ hpos hμ1 σ hσ] with u hu
  simp only [Set.mem_iUnion] at hu
  obtain ⟨y, hy⟩ := hu
  rw [adaptiveCode_eq_of_mem μ σ hσ u y hy, Finset.sum_eq_single y]
  · rw [Set.indicator_of_mem hy]
    ring
  · intro x _ hxy
    rw [Set.indicator_of_notMem]
    · ring
    · intro hx
      exact hxy (codeMap_eq_unique_of_predictable μ σ hσ u hx hy)
  · intro hyu
    exact absurd (Finset.mem_univ y) hyu


lemma aestronglyMeasurable_observable_adaptiveCode (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (g : ConfigSpace E → ℝ) :
    AEStronglyMeasurable (fun u => g (adaptiveCode μ σ u)) (Vcube n) := by
  apply AEStronglyMeasurable.congr _
    (observable_adaptiveCode_ae μ hpos hμ1 σ hσ g).symm
  apply Measurable.aestronglyMeasurable
  apply Finset.measurable_sum
  intro x _
  exact measurable_const.mul
    (measurable_const.indicator (measurableSet_adaptiveFibre μ σ x))


theorem integral_g_adaptiveCode (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (g : ConfigSpace E → ℝ) :
    ∫ u, g (adaptiveCode μ σ u) ∂(Vcube n) = ∑ x, g x * μ x := by
  rw [integral_congr_ae (observable_adaptiveCode_ae μ hpos hμ1 σ hσ g), integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [integral_const_mul,
      integral_indicator_const (1 : ℝ) (measurableSet_adaptiveFibre μ σ x), smul_eq_mul,
      mul_one]
    show g x * ((Vcube n) (adaptiveFibre μ σ x)).toReal = g x * μ x
    rw [vcube_adaptiveFibre μ hpos hμ1 σ x]
  · intro x _
    exact Integrable.const_mul
      (Integrable.indicator (integrable_const 1) (measurableSet_adaptiveFibre μ σ x)) _


theorem integral_g_adaptiveCode_Wt (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (g : ConfigSpace E → ℝ) (s : ℕ) :
    ∫ p, g (adaptiveCode μ σ (Wt p.1 p.2 s)) ∂((Vcube n).prod (Vcube n)) =
      ∑ x, g x * μ x := by
  have hmp := selMap_measurePreserving n s
  have hcomp :
      ∫ p, (fun w => g (adaptiveCode μ σ w)) (selMap n s p)
          ∂((Vcube n).prod (Vcube n)) =
        ∫ w, g (adaptiveCode μ σ w) ∂(Vcube n) := by
    have hae := aestronglyMeasurable_observable_adaptiveCode μ hpos hμ1 σ hσ g
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable, hmp.map_eq]
    rwa [hmp.map_eq]
  have hrw : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (fun w => g (adaptiveCode μ σ w)) (selMap n s p)) =
      (fun p => g (adaptiveCode μ σ (Wt p.1 p.2 s))) := by
    funext p
    rw [show p = (p.1, p.2) from rfl, selMap_eq_Wt]
  rw [hrw] at hcomp
  rw [hcomp, integral_g_adaptiveCode μ hpos hμ1 σ hσ g]


theorem integral_g_independent_randomOrder (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (order : (Fin n → ℝ) → (Fin n ≃ E)) (g : ConfigSpace E → ℝ) :
    ∫ U, (∫ V, g (codeMap μ (order U : Fin n → E) V) ∂(Vcube n)) ∂(Vcube n) =
      ∑ x, g x * μ x := by
  have hinner : ∀ U : Fin n → ℝ,
      (∫ V, g (codeMap μ (order U : Fin n → E) V) ∂(Vcube n)) =
        ∑ x, g x * μ x := by
    intro U
    exact integral_g_codeMap μ hpos hμ1 (order U) g
  simp_rw [hinner]
  rw [integral_const]
  simp


theorem integral_g_frozenOrder_Wt_zero (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ)
    (g : ConfigSpace E → ℝ) :
    ∫ U, (∫ V, g (codeMap μ (σ (adaptiveCode μ σ U) : Fin n → E)
        (Wt U V 0)) ∂(Vcube n)) ∂(Vcube n) = ∑ x, g x * μ x := by
  calc
    ∫ U, (∫ V, g (codeMap μ (σ (adaptiveCode μ σ U) : Fin n → E)
        (Wt U V 0)) ∂(Vcube n)) ∂(Vcube n)
        = ∫ U, g (adaptiveCode μ σ U) ∂(Vcube n) := by
          apply integral_congr_ae
          filter_upwards
            [codeMap_selectedOrder_eq_adaptiveCode_ae μ hpos hμ1 σ hσ] with U hU
          simp only [Wt_zero, hU]
          rw [integral_const]
          simp
    _ = ∑ x, g x * μ x := integral_g_adaptiveCode μ hpos hμ1 σ hσ g


theorem integral_g_frozenOrder_Wt_card (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (g : ConfigSpace E → ℝ) :
    ∫ U, (∫ V, g (codeMap μ (σ (adaptiveCode μ σ U) : Fin n → E)
        (Wt U V n)) ∂(Vcube n)) ∂(Vcube n) = ∑ x, g x * μ x := by
  simpa only [Wt_card] using
    integral_g_independent_randomOrder μ hpos hμ1
      (fun U => σ (adaptiveCode μ σ U)) g

end AdaptiveCodingLaw
end OSSS
end StatMech
