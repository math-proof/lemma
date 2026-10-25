/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.Probability.ContinuousFKG.Part3
import Def.StatisticalMechanics.Code.OSSS.GrandCoupling.Part3
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace GrandCoupling

open OSSS.Monotonic OSSS.Coding StatMech.Probability

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma Wt_mono_V {n : ℕ} (U : Fin n → ℝ) (s : ℕ) :
    Monotone (fun V : Fin n → ℝ => Wt U V s) := by
  intro V V' hle i
  unfold Wt
  by_cases h : (i : ℕ) < s
  · simp only [h, if_true]; exact hle i
  · simp only [h, if_false]; exact le_refl _


lemma measurable_Wt {n : ℕ} (U : Fin n → ℝ) (s : ℕ) :
    Measurable (fun V : Fin n → ℝ => Wt U V s) := by
  apply measurable_pi_lambda
  intro i; unfold Wt
  by_cases h : (i : ℕ) < s
  · simp only [h, if_true]; exact measurable_pi_apply i
  · simp only [h, if_false]; exact measurable_const


lemma f_codeMap_mono {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (U : Fin n → ℝ) (s : ℕ) :
    Monotone (fun V : Fin n → ℝ => f (codeMap μ σ (Wt U V s))) :=
  fun _ _ hle => hf ((codeMap_mono_u hpos hmono σ) ((Wt_mono_V U s) hle))


lemma coord_codeMap_mono {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) (e : E) (U : Fin n → ℝ) (s : ℕ) :
    Monotone (fun V : Fin n → ℝ => Lindeberg.coord e (codeMap μ σ (Wt U V s))) :=
  fun _ _ hle => Lindeberg.coord_mono e ((codeMap_mono_u hpos hmono σ) ((Wt_mono_V U s) hle))


lemma measurable_f_codeMap_Wt (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (s : ℕ) :
    Measurable (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (Wt U V s))) :=
  (measurable_g_codeMap μ σ f).comp (measurable_Wt U s)


lemma measurable_coord_codeMap_Wt (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (e : E) (U : Fin n → ℝ) (s : ℕ) :
    Measurable (fun V : Fin n → ℝ => Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s))) :=
  (measurable_g_codeMap μ σ (Lindeberg.coord e)).comp (measurable_Wt U s)


lemma abs_coord_le_one (e : E) (ω : ConfigSpace E) : |Lindeberg.coord e ω| ≤ 1 := by
  unfold Lindeberg.coord; split <;> norm_num


theorem grandCoupling_fkg_cross {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (U : Fin n → ℝ)
    (s₁ s₂ : ℕ) :
    (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s₁)) ∂(Vcube n))
        * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂)) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s₁))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂)) ∂(Vcube n) := by
  unfold Vcube
  refine continuous_fkg n
    (measurable_f_codeMap_Wt μ σ f U s₁)
    (measurable_coord_codeMap_Wt μ σ e U s₂)
    (fun V => hfC _)
    (fun V => abs_coord_le_one e _)
    (f_codeMap_mono hpos hmono (σ : Fin n → E) hf U s₁)
    (coord_codeMap_mono hpos hmono (σ : Fin n → E) e U s₂)


theorem osss_grand_coupling {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (U : Fin n → ℝ) (t : ℕ) :
    ((∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n))
        * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t - 1)))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
    ∧ ((∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
        * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n)) :=
  ⟨grandCoupling_fkg_cross hpos hmono σ hf hfC e U (t - 1) t,
   grandCoupling_fkg_cross hpos hmono σ hf hfC e U t (t - 1)⟩


section FK

open StatMech.OSSS.MonotonicFK


theorem fk_codeMap_mono {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) {n : ℕ} (σ : Fin n → Sym2 V) :
    Monotone (fun u : Fin n → ℝ => codeMap (fkMass G p q) σ u) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact codeMap_mono_u (fun ω => fkMass_pos G hp hp1 hq0 ω) (fkMass_isMonotonic G hp hp1 hq) σ


theorem fk_grandCoupling_fkg_cross {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    {f : ConfigSpace (Sym2 V) → ℝ} (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf)
    (e : Sym2 V) (U : Fin n → ℝ) (s₁ s₂ : ℕ) :
    (∫ Vv, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) (Wt U Vv s₁)) ∂(Vcube n))
        * (∫ Vv, Lindeberg.coord e (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) (Wt U Vv s₂)) ∂(Vcube n))
      ≤ ∫ Vv, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) (Wt U Vv s₁))
            * Lindeberg.coord e (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) (Wt U Vv s₂)) ∂(Vcube n) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact grandCoupling_fkg_cross (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_isMonotonic G hp hp1 hq) σ hf hfC e U s₁ s₂

end FK
end GrandCoupling
end OSSS
end StatMech
