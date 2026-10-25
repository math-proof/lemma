/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
import Theorem.StatisticalMechanics.Code.OSSS.PredictableTreeQuery
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part34
open scoped BigOperators
open MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace OSSS

namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem integral_eq_sum_fibre {α β : Type*} [MeasurableSpace α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (ν : Measure α) [IsFiniteMeasure ν] (φ : α → β) (hφ : Measurable φ)
    (g : β → ℝ) :
    (∫ x, g (φ x) ∂ν) = ∑ y, g y * (ν {x | φ x = y}).toReal := by
  have hms : ∀ y : β, MeasurableSet {x : α | φ x = y} :=
    fun y => hφ (measurableSet_singleton y)
  have hpoint : (fun x => g (φ x)) =
      (fun x => ∑ y, g y * Set.indicator {x' | φ x' = y} (fun _ => (1 : ℝ)) x) := by
    funext x
    rw [Finset.sum_eq_single (φ x)]
    · rw [Set.indicator_of_mem (by simp)]
      ring
    · intro y _ hy
      rw [Set.indicator_of_notMem]
      · ring
      · simpa only [Set.mem_setOf_eq] using Ne.symm hy
    · simp
  rw [hpoint, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y _
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) (hms y),
      smul_eq_mul, mul_one]
    rfl
  · intro y _
    exact Integrable.const_mul
      (Integrable.indicator (integrable_const (1 : ℝ)) (hms y)) _


theorem pairedCube_causal_integral_eq_atom_sum (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    (∫ z, (if (pairedCausalOutputs mu S base z).1 = base then
        g (pairedCausalOutputs mu S base z).2.1
          (pairedCausalOutputs mu S base z).2.2 else 0)
      ∂(pairedCube (Fintype.card E))) =
      ∑ left, ∑ right, g left right *
        (pairedCube (Fintype.card E)
          (frozenTripleCodeAtom mu S base left right)).toReal := by
  letI : IsFiniteMeasure (pairedCube (Fintype.card E)) :=
    ⟨by rw [pairedCube, Measure.pi_univ]; simp⟩
  rw [integral_eq_sum_fibre (pairedCube (Fintype.card E))
    (pairedCausalOutputs mu S base) (measurable_pairedCausalOutputs mu S base)
    (fun y => if y.1 = base then g y.2.1 y.2.2 else 0)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single base]
  · simp only [if_pos]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro left _
    apply Finset.sum_congr rfl
    intro right _
    rw [pairedCausalOutputs_fibre]
  · intro b _ hne
    simp [hne]
  · simp


theorem pairedCube_causal_integral_eq_tripleJointProb
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    (∫ z, (if (pairedCausalOutputs mu S base z).1 = base then
        g (pairedCausalOutputs mu S base z).2.1
          (pairedCausalOutputs mu S base z).2.2 else 0)
      ∂(pairedCube (Fintype.card E))) =
      ∑ left, ∑ right, g left right *
        tripleJointProb mu ∅ base left right S := by
  rw [pairedCube_causal_integral_eq_atom_sum]
  simp_rw [pairedCube_frozenTripleCodeAtom_toReal_eq_tripleJointProb mu hpos]


theorem tripleCube_causal_integral_eq_atom_sum (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    (∫ z, (if (tripleCausalOutputs μ S base z).1 = base then
        g (tripleCausalOutputs μ S base z).2.1
          (tripleCausalOutputs μ S base z).2.2 else 0)
      ∂(tripleCube (Fintype.card E))) =
      ∑ left, ∑ right, g left right *
        (tripleCube (Fintype.card E)
          (frozenCrossCodeAtom μ S base left right)).toReal := by
  letI : IsFiniteMeasure (tripleCube (Fintype.card E)) :=
    ⟨by rw [tripleCube, Measure.pi_univ]; simp⟩
  rw [integral_eq_sum_fibre (tripleCube (Fintype.card E))
    (tripleCausalOutputs μ S base) (measurable_tripleCausalOutputs μ S base)
    (fun y => if y.1 = base then g y.2.1 y.2.2 else 0)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single base]
  · simp only [if_pos]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro left _
    apply Finset.sum_congr rfl
    intro right _
    rw [tripleCausalOutputs_fibre]
  · intro b _ hne
    simp [hne]
  · simp


theorem tripleCube_causal_integral_eq_crossTripleJointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    (∫ z, (if (tripleCausalOutputs μ S base z).1 = base then
        g (tripleCausalOutputs μ S base z).2.1
          (tripleCausalOutputs μ S base z).2.2 else 0)
      ∂(tripleCube (Fintype.card E))) =
      ∑ left, ∑ right, g left right *
        crossTripleJointProb μ ∅ base left right S := by
  rw [tripleCube_causal_integral_eq_atom_sum]
  simp_rw [tripleCube_frozenCrossCodeAtom_toReal_eq_crossTripleJointProb μ hpos]


theorem pairedCube_causal_integral_pullback (mu : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    (∫ z, (if (pairedCausalOutputs mu S base z).1 = base then
        g (pairedCausalOutputs mu S base z).2.1
          (pairedCausalOutputs mu S base z).2.2 else 0)
      ∂(pairedCube (Fintype.card E))) =
    ∫ p, (if codeMap mu (realizedEquiv S.leftOrder base :
          Fin (Fintype.card E) → E) p.1 = base then
        g (codeMap mu (realizedEquiv S.leftOrder base :
            Fin (Fintype.card E) → E)
              (causalMixLabels S.leftOrder base p.1 p.2))
          (codeMap mu (realizedEquiv S.leftOrder base :
            Fin (Fintype.card E) → E)
              (causalMixLabels S.rightOrder base p.1 p.2)) else 0)
      ∂((GrandCoupling.Vcube (Fintype.card E)).prod
        (GrandCoupling.Vcube (Fintype.card E))) := by
  have hmp := pairedCube_measurePreserving (Fintype.card E)
  rw [← hmp.integral_comp' (fun p =>
    if codeMap mu (realizedEquiv S.leftOrder base :
        Fin (Fintype.card E) → E) p.1 = base then
      g (codeMap mu (realizedEquiv S.leftOrder base :
          Fin (Fintype.card E) → E)
            (causalMixLabels S.leftOrder base p.1 p.2))
        (codeMap mu (realizedEquiv S.leftOrder base :
          Fin (Fintype.card E) → E)
            (causalMixLabels S.rightOrder base p.1 p.2)) else 0)]
  rfl


theorem tripleCube_causal_integral_pullback (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    (∫ z, (if (tripleCausalOutputs μ S base z).1 = base then
        g (tripleCausalOutputs μ S base z).2.1
          (tripleCausalOutputs μ S base z).2.2 else 0)
      ∂(tripleCube (Fintype.card E))) =
    ∫ q, (if codeMap μ (realizedEquiv S.leftOrder base :
          Fin (Fintype.card E) → E) q.1.1 = base then
        g (codeMap μ (realizedEquiv S.leftOrder base :
            Fin (Fintype.card E) → E)
              (causalMixLabels S.leftOrder base q.1.1 q.1.2))
          (codeMap μ (realizedEquiv S.leftOrder base :
            Fin (Fintype.card E) → E)
              (causalMixLabels S.rightOrder base q.1.1 q.2)) else 0)
      ∂(((GrandCoupling.Vcube (Fintype.card E)).prod
        (GrandCoupling.Vcube (Fintype.card E))).prod
          (GrandCoupling.Vcube (Fintype.card E))) := by
  let G := fun q : ((Fin (Fintype.card E) → ℝ) ×
      (Fin (Fintype.card E) → ℝ)) × (Fin (Fintype.card E) → ℝ) =>
    if codeMap μ (realizedEquiv S.leftOrder base :
        Fin (Fintype.card E) → E) q.1.1 = base then
      g (codeMap μ (realizedEquiv S.leftOrder base :
          Fin (Fintype.card E) → E)
            (causalMixLabels S.leftOrder base q.1.1 q.1.2))
        (codeMap μ (realizedEquiv S.leftOrder base :
          Fin (Fintype.card E) → E)
            (causalMixLabels S.rightOrder base q.1.1 q.2)) else 0
  change (∫ z, G (tripleCubeEquiv (Fintype.card E) z)
      ∂(tripleCube (Fintype.card E))) = _
  exact tripleCube_integral_equiv (Fintype.card E) G


theorem tripleCube_conditional_product {n : ℕ}
    (A : (Fin n → ℝ) → ℝ)
    (F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hAm : Measurable A) (hFm : Measurable (Function.uncurry F))
    (hGm : Measurable (Function.uncurry G))
    {CA CF CG : ℝ} (hAC : ∀ U, |A U| ≤ CA)
    (hFC : ∀ U V, |F U V| ≤ CF) (hGC : ∀ U V, |G U V| ≤ CG) :
    (∫ q, A q.1.1 * F q.1.1 q.1.2 * G q.1.1 q.2
      ∂((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)).prod
        (GrandCoupling.Vcube n)) =
      ∫ U, A U * (∫ V, F U V ∂(GrandCoupling.Vcube n)) *
        (∫ V, G U V ∂(GrandCoupling.Vcube n))
        ∂(GrandCoupling.Vcube n) := by
  have hCA0 : 0 ≤ CA := le_trans (abs_nonneg _) (hAC 0)
  have hCF0 : 0 ≤ CF := le_trans (abs_nonneg _) (hFC 0 0)
  let H := fun q : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
    A q.1.1 * F q.1.1 q.1.2 * G q.1.1 q.2
  have hHm : Measurable H :=
    ((hAm.comp (measurable_fst.comp measurable_fst)).mul
      (hFm.comp measurable_fst)).mul
      (hGm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hHC : ∀ q, |H q| ≤ (CA * CF) * CG := by
    intro q
    simp only [H, abs_mul]
    exact mul_le_mul (mul_le_mul (hAC _) (hFC _ _) (abs_nonneg _) hCA0)
      (hGC _ _) (abs_nonneg _) (mul_nonneg hCA0 hCF0)
  have hHi : Integrable H (((GrandCoupling.Vcube n).prod
      (GrandCoupling.Vcube n)).prod (GrandCoupling.Vcube n)) :=
    StatMech.Probability.ContinuousFKG.integrable_of_bdd _ hHm hHC
  rw [show (fun q => A q.1.1 * F q.1.1 q.1.2 * G q.1.1 q.2) = H from rfl]
  rw [integral_prod H hHi]
  have hinner (p : (Fin n → ℝ) × (Fin n → ℝ)) :
      (∫ y, H (p, y) ∂(GrandCoupling.Vcube n)) =
        A p.1 * F p.1 p.2 * (∫ y, G p.1 y ∂(GrandCoupling.Vcube n)) := by
    simp only [H]
    rw [integral_const_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
  have hK : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      A p.1 * F p.1 p.2 * (∫ V, G p.1 V ∂(GrandCoupling.Vcube n)))
      ((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)) := by
    have heq : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        A p.1 * F p.1 p.2 * (∫ V, G p.1 V ∂(GrandCoupling.Vcube n))) =
        (fun p => ∫ y, H (p, y) ∂(GrandCoupling.Vcube n)) := by
      funext p
      exact (hinner p).symm
    rw [heq]
    exact hHi.integral_prod_left
  rw [integral_prod _ hK]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro U
  change (∫ y, A U * F U y * (∫ V, G U V ∂(GrandCoupling.Vcube n))
      ∂(GrandCoupling.Vcube n)) = _
  rw [show (fun y => A U * F U y * (∫ V, G U V ∂(GrandCoupling.Vcube n))) =
      (fun y => (A U * (∫ V, G U V ∂(GrandCoupling.Vcube n))) * F U y) by
        funext y; ring]
  rw [integral_const_mul]
  ring


theorem tripleCube_product_le_pairedCube_product {mu : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < mu ω) (hmono : IsMonotonicMeasure mu)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) {Cf : ℝ}
    (hfC : ∀ ω, |f ω| ≤ Cf)
    {g : ConfigSpace E → ℝ} (hg : Monotone g) {Cg : ℝ}
    (hgC : ∀ ω, |g ω| ≤ Cg) :
    (∫ z, (if (tripleCausalOutputs mu S base z).1 = base then
        f (tripleCausalOutputs mu S base z).2.1 *
          g (tripleCausalOutputs mu S base z).2.2 else 0)
      ∂(tripleCube (Fintype.card E))) ≤
    ∫ z, (if (pairedCausalOutputs mu S base z).1 = base then
        f (pairedCausalOutputs mu S base z).2.1 *
          g (pairedCausalOutputs mu S base z).2.2 else 0)
      ∂(pairedCube (Fintype.card E)) := by
  let n := Fintype.card E
  let σ := realizedEquiv S.leftOrder base
  let A : (Fin n → ℝ) → ℝ := fun U =>
    if codeMap mu (σ : Fin n → E) U = base then 1 else 0
  let F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun U V =>
    f (codeMap mu (σ : Fin n → E) (causalMixLabels S.leftOrder base U V))
  let G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun U V =>
    g (codeMap mu (σ : Fin n → E) (causalMixLabels S.rightOrder base U V))
  have hset : MeasurableSet {U : Fin n → ℝ |
      codeMap mu (σ : Fin n → E) U = base} :=
    (GrandCoupling.measurable_codeMap mu σ) (measurableSet_singleton base)
  have hAm : Measurable A := by
    unfold A
    exact Measurable.ite hset measurable_const measurable_const
  have hFm : Measurable (Function.uncurry F) :=
    (GrandCoupling.measurable_g_codeMap mu σ f).comp
      (measurable_causalMixLabels_prod S.leftOrder base)
  have hGm : Measurable (Function.uncurry G) :=
    (GrandCoupling.measurable_g_codeMap mu σ g).comp
      (measurable_causalMixLabels_prod S.rightOrder base)
  have hAC : ∀ U, |A U| ≤ (1 : ℝ) := by
    intro U
    unfold A
    split <;> norm_num
  have hFC : ∀ U V, |F U V| ≤ Cf := fun U V => hfC _
  have hGC : ∀ U V, |G U V| ≤ Cg := fun U V => hgC _
  have hcond := StatMech.Probability.fkg_second_block
    (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => A p.1 * F p.1 p.2)
    (g := fun p : (Fin n → ℝ) × (Fin n → ℝ) => G p.1 p.2)
    (hAm.comp measurable_fst |>.mul hFm) hGm
    (Cf := Cf) (Cg := Cg)
    (fun p => by
      rw [abs_mul]
      calc
        |A p.1| * |F p.1 p.2| ≤ 1 * |F p.1 p.2| :=
          mul_le_mul_of_nonneg_right (hAC _) (abs_nonneg _)
        _ ≤ Cf := by simpa using hFC p.1 p.2)
    (fun p => hGC p.1 p.2)
    (fun U V V' hVV => mul_le_mul_of_nonneg_left
      (hf (GrandCoupling.codeMap_mono_u hpos hmono _
        (causalMixLabels_mono_right S.leftOrder base U hVV))) (by
          unfold A
          split <;> norm_num))
    (fun U V V' hVV => hg (GrandCoupling.codeMap_mono_u hpos hmono _
      (causalMixLabels_mono_right S.rightOrder base U hVV)))
  have htriple := tripleCube_conditional_product A F G hAm hFm hGm hAC hFC hGC
  rw [tripleCube_causal_integral_pullback
    (g := fun left right => f left * g right)]
  rw [pairedCube_causal_integral_pullback
    (g := fun left right => f left * g right)]
  simp only [A, F, G, n, σ, ite_mul, one_mul, zero_mul] at htriple hcond ⊢
  rw [htriple]
  rw [StatMech.Probability.cube_eq] at hcond
  have hnorm :
      (∫ U, A U * (∫ V, F U V ∂(GrandCoupling.Vcube n)) *
        (∫ V, G U V ∂(GrandCoupling.Vcube n))
        ∂(GrandCoupling.Vcube n)) =
      ∫ U, (∫ V, A U * F U V ∂(GrandCoupling.Vcube n)) *
        (∫ V, G U V ∂(GrandCoupling.Vcube n))
        ∂(GrandCoupling.Vcube n) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro U
    change (A U * (∫ V, F U V ∂(GrandCoupling.Vcube n))) *
      (∫ V, G U V ∂(GrandCoupling.Vcube n)) =
      (∫ V, A U * F U V ∂(GrandCoupling.Vcube n)) *
      (∫ V, G U V ∂(GrandCoupling.Vcube n))
    rw [integral_const_mul]
  have hcond' :
      (∫ U, (∫ V, A U * F U V ∂(GrandCoupling.Vcube n)) *
        (∫ V, G U V ∂(GrandCoupling.Vcube n))
        ∂(GrandCoupling.Vcube n)) ≤
      ∫ p, (A p.1 * F p.1 p.2) * G p.1 p.2
        ∂((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)) := by
    simpa only [A, F, G, n, σ, ite_mul, one_mul, zero_mul] using hcond
  have hfinal := hnorm.trans_le hcond'
  simpa only [A, F, G, n, σ, ite_mul, one_mul, zero_mul] using hfinal


theorem no_flip_causal_atom_eq_zero
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (hno : ∀ e, tripleModeAt S base e ≠ .flip)
    (f : ConfigSpace E → ℝ) :
    (∑ left, ∑ right, |f right - f left| *
      tripleJointProb mu ∅ base left right S) = 0 := by
  rw [← pairedCube_causal_integral_eq_tripleJointProb mu hpos S base
    (fun left right => |f right - f left|)]
  rw [pairedCube_causal_integral_pullback mu S base
    (fun left right => |f right - f left|)]
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro p
  change (if codeMap mu (realizedEquiv S.leftOrder base :
      Fin (Fintype.card E) → E) p.1 = base then
    |f (codeMap mu (realizedEquiv S.leftOrder base :
        Fin (Fintype.card E) → E)
          (causalMixLabels S.rightOrder base p.1 p.2)) -
      f (codeMap mu (realizedEquiv S.leftOrder base :
        Fin (Fintype.card E) → E)
          (causalMixLabels S.leftOrder base p.1 p.2))| else 0) = 0
  have hlabels := causalMixLabels_leftOrder_eq_rightOrder_of_no_flip
    S base hno p.1 p.2
  rw [hlabels]
  simp


theorem decisionTree_flip_atom_step_le
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (hmono : IsMonotonicMeasure mu) (T : DecisionTree E) (t : ℕ)
    (hf : Monotone T.evalR) (base : ConfigSpace E) (e : E)
    (he : tripleModeAt
      (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) base e = .flip) :
    let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
    (∑ left, ∑ right, |T.evalR right - T.evalR left| *
        tripleJointProb mu ∅ base left right S) ≤
      (∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e left +
          T.evalR right * Lindeberg.coord e right) *
            tripleJointProb mu ∅ base left right S) -
      (∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e right +
          T.evalR right * Lindeberg.coord e left) *
            crossTripleJointProb mu ∅ base left right S) := by
  dsimp only
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
  have hcross₁ := tripleCube_product_le_pairedCube_product hpos hmono S base
    (f := T.evalR) hf (Cf := 1)
    (fun ω => by unfold DecisionTree.evalR; split <;> norm_num)
    (g := Lindeberg.coord e) (Lindeberg.coord_mono e) (Cg := 1)
    (GrandCoupling.abs_coord_le_one e)
  have hcross₂ := tripleCube_product_le_pairedCube_product hpos hmono S base
    (f := Lindeberg.coord e) (Lindeberg.coord_mono e) (Cf := 1)
    (GrandCoupling.abs_coord_le_one e)
    (g := T.evalR) hf (Cg := 1)
    (fun ω => by unfold DecisionTree.evalR; split <;> norm_num)
  have hc₁ :
      (∑ left, ∑ right, T.evalR left * Lindeberg.coord e right *
        crossTripleJointProb mu ∅ base left right S) ≤
      ∑ left, ∑ right, T.evalR left * Lindeberg.coord e right *
        tripleJointProb mu ∅ base left right S := by
    rw [← tripleCube_causal_integral_eq_crossTripleJointProb mu hpos S base
      (fun left right => T.evalR left * Lindeberg.coord e right)]
    rw [← pairedCube_causal_integral_eq_tripleJointProb mu hpos S base
      (fun left right => T.evalR left * Lindeberg.coord e right)]
    exact hcross₁
  have hc₂ :
      (∑ left, ∑ right, T.evalR right * Lindeberg.coord e left *
        crossTripleJointProb mu ∅ base left right S) ≤
      ∑ left, ∑ right, T.evalR right * Lindeberg.coord e left *
        tripleJointProb mu ∅ base left right S := by
    rw [← tripleCube_causal_integral_eq_crossTripleJointProb mu hpos S base
      (fun left right => T.evalR right * Lindeberg.coord e left)]
    rw [← pairedCube_causal_integral_eq_tripleJointProb mu hpos S base
      (fun left right => T.evalR right * Lindeberg.coord e left)]
    simpa [mul_comm] using hcross₂
  have hcommon :
      (∑ left, ∑ right, |T.evalR right - T.evalR left| *
        tripleJointProb mu ∅ base left right S) =
      ∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e left +
          T.evalR right * Lindeberg.coord e right -
          T.evalR left * Lindeberg.coord e right -
          T.evalR right * Lindeberg.coord e left) *
            tripleJointProb mu ∅ base left right S := by
    rw [← pairedCube_causal_integral_eq_tripleJointProb mu hpos S base
      (fun left right => |T.evalR right - T.evalR left|)]
    rw [← pairedCube_causal_integral_eq_tripleJointProb mu hpos S base
      (fun left right => T.evalR left * Lindeberg.coord e left +
        T.evalR right * Lindeberg.coord e right -
        T.evalR left * Lindeberg.coord e right -
        T.evalR right * Lindeberg.coord e left)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    by_cases hb : (pairedCausalOutputs mu S base z).1 = base
    · simp only [hb, if_true]
      exact causal_abs_eq_four_terms hpos hmono hf
        t T base (fun i => (z i).1) (fun i => (z i).2) e he
    · simp [hb]
  rw [hcommon]
  have hsplitCommon :
      (∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e left +
          T.evalR right * Lindeberg.coord e right -
          T.evalR left * Lindeberg.coord e right -
          T.evalR right * Lindeberg.coord e left) *
            tripleJointProb mu ∅ base left right S) =
      (∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e left +
          T.evalR right * Lindeberg.coord e right) *
            tripleJointProb mu ∅ base left right S) -
      (∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e right +
          T.evalR right * Lindeberg.coord e left) *
            tripleJointProb mu ∅ base left right S) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro left _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro right _
    ring
  rw [hsplitCommon]
  have hcrossSum :
      (∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e right +
          T.evalR right * Lindeberg.coord e left) *
            crossTripleJointProb mu ∅ base left right S) ≤
      ∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e right +
          T.evalR right * Lindeberg.coord e left) *
            tripleJointProb mu ∅ base left right S := by
    simp_rw [add_mul, Finset.sum_add_distrib]
    exact add_le_add hc₁ hc₂
  linarith


theorem causal_fkg_cross_fiber {mu : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < mu ω) (hmono : IsMonotonicMeasure mu)
    (S₁ S₂ : CausalOrder (Finset.univ : Finset E))
    (base : ConfigSpace E) (σ : Fin (Fintype.card E) ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) {Cf : ℝ}
    (hfC : ∀ ω, |f ω| ≤ Cf) (e : E)
    (U : Fin (Fintype.card E) → ℝ) :
    (∫ V, f (codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S₁ base U V)) ∂(GrandCoupling.Vcube (Fintype.card E))) *
        (∫ V, Lindeberg.coord e
          (codeMap mu (σ : Fin (Fintype.card E) → E)
            (causalMixLabels S₂ base U V)) ∂(GrandCoupling.Vcube (Fintype.card E))) ≤
      ∫ V, f (codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S₁ base U V)) * Lindeberg.coord e
          (codeMap mu (σ : Fin (Fintype.card E) → E)
            (causalMixLabels S₂ base U V)) ∂(GrandCoupling.Vcube (Fintype.card E)) := by
  refine StatMech.Probability.fkg_second_block_fiber
    (f := fun p : (Fin (Fintype.card E) → ℝ) ×
      (Fin (Fintype.card E) → ℝ) =>
        f (codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S₁ base p.1 p.2)))
    (g := fun p : (Fin (Fintype.card E) → ℝ) ×
      (Fin (Fintype.card E) → ℝ) => Lindeberg.coord e
        (codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels S₂ base p.1 p.2)))
    ((GrandCoupling.measurable_g_codeMap mu σ f).comp
      (measurable_causalMixLabels_prod S₁ base))
    ((GrandCoupling.measurable_g_codeMap mu σ (Lindeberg.coord e)).comp
      (measurable_causalMixLabels_prod S₂ base))
    (Cf := Cf) (Cg := 1) (fun z => hfC _)
    (fun z => GrandCoupling.abs_coord_le_one e _) ?_ ?_ U
  · intro Ufix V V' hVV
    exact hf (GrandCoupling.codeMap_mono_u hpos hmono _
      (causalMixLabels_mono_right S₁ base Ufix hVV))
  · intro Ufix V V' hVV
    exact Lindeberg.coord_mono e (GrandCoupling.codeMap_mono_u hpos hmono _
      (causalMixLabels_mono_right S₂ base Ufix hVV))


theorem causal_abs_integral_fiber_le {mu : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < mu ω) (hmono : IsMonotonicMeasure mu)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) {Cf : ℝ}
    (hfC : ∀ ω, |f ω| ≤ Cf) (t : ℕ) (T : DecisionTree E)
    (base : ConfigSpace E) (e : E)
    (he : tripleModeAt
      (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) base e = .flip)
    (U : Fin (Fintype.card E) → ℝ) :
    let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
    let σ := realizedEquiv S.leftOrder base
    let Yl := fun V => codeMap mu (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.leftOrder base U V)
    let Yr := fun V => codeMap mu (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.rightOrder base U V)
    (∫ V, |f (Yr V) - f (Yl V)| ∂(GrandCoupling.Vcube (Fintype.card E))) ≤
      (∫ V, f (Yl V) * Lindeberg.coord e (Yl V)
        ∂(GrandCoupling.Vcube (Fintype.card E))) +
      (∫ V, f (Yr V) * Lindeberg.coord e (Yr V)
        ∂(GrandCoupling.Vcube (Fintype.card E))) -
      (∫ V, f (Yl V) ∂(GrandCoupling.Vcube (Fintype.card E))) *
        (∫ V, Lindeberg.coord e (Yr V)
          ∂(GrandCoupling.Vcube (Fintype.card E))) -
      (∫ V, f (Yr V) ∂(GrandCoupling.Vcube (Fintype.card E))) *
        (∫ V, Lindeberg.coord e (Yl V)
          ∂(GrandCoupling.Vcube (Fintype.card E))) := by
  dsimp only
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
  let σ := realizedEquiv S.leftOrder base
  let Yl := fun V => codeMap mu (σ : Fin (Fintype.card E) → E)
    (causalMixLabels S.leftOrder base U V)
  let Yr := fun V => codeMap mu (σ : Fin (Fintype.card E) → E)
    (causalMixLabels S.rightOrder base U V)
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hfC (fun _ => false))
  have hInt (C₁ C₂ : CausalOrder (Finset.univ : Finset E)) :
      Integrable (fun V =>
        f (codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels C₁ base U V)) * Lindeberg.coord e
        (codeMap mu (σ : Fin (Fintype.card E) → E)
          (causalMixLabels C₂ base U V)))
        (GrandCoupling.Vcube (Fintype.card E)) := by
    refine StatMech.Probability.ContinuousFKG.integrable_of_bdd _
      (((GrandCoupling.measurable_g_codeMap mu σ f).comp
        (measurable_causalMixLabels_right C₁ base U)).mul
       ((GrandCoupling.measurable_g_codeMap mu σ (Lindeberg.coord e)).comp
        (measurable_causalMixLabels_right C₂ base U))) (C := Cf * 1) ?_
    intro V
    rw [abs_mul]
    exact mul_le_mul (hfC _) (GrandCoupling.abs_coord_le_one e _)
      (abs_nonneg _) hCf0
  have hEq : (∫ V, |f (Yr V) - f (Yl V)|
        ∂(GrandCoupling.Vcube (Fintype.card E))) =
      (∫ V, f (Yl V) * Lindeberg.coord e (Yl V)
        ∂(GrandCoupling.Vcube (Fintype.card E))) +
      (∫ V, f (Yr V) * Lindeberg.coord e (Yr V)
        ∂(GrandCoupling.Vcube (Fintype.card E))) -
      (∫ V, f (Yl V) * Lindeberg.coord e (Yr V)
        ∂(GrandCoupling.Vcube (Fintype.card E))) -
      (∫ V, f (Yr V) * Lindeberg.coord e (Yl V)
        ∂(GrandCoupling.Vcube (Fintype.card E))) := by
    let A := fun V => f (Yl V) * Lindeberg.coord e (Yl V)
    let B := fun V => f (Yr V) * Lindeberg.coord e (Yr V)
    let C := fun V => f (Yl V) * Lindeberg.coord e (Yr V)
    let D := fun V => f (Yr V) * Lindeberg.coord e (Yl V)
    have hpoint : ∀ V, |f (Yr V) - f (Yl V)| =
        A V + B V - C V - D V := by
      intro V
      exact causal_abs_eq_four_terms hpos hmono hf t T base U V e he
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    have hA : Integrable A (GrandCoupling.Vcube (Fintype.card E)) :=
      hInt S.leftOrder S.leftOrder
    have hB : Integrable B (GrandCoupling.Vcube (Fintype.card E)) :=
      hInt S.rightOrder S.rightOrder
    have hC : Integrable C (GrandCoupling.Vcube (Fintype.card E)) :=
      hInt S.leftOrder S.rightOrder
    have hD : Integrable D (GrandCoupling.Vcube (Fintype.card E)) :=
      hInt S.rightOrder S.leftOrder
    change (∫ V, (((A + B) - C) - D) V
      ∂(GrandCoupling.Vcube (Fintype.card E))) =
      (∫ V, A V ∂(GrandCoupling.Vcube (Fintype.card E))) +
      (∫ V, B V ∂(GrandCoupling.Vcube (Fintype.card E))) -
      (∫ V, C V ∂(GrandCoupling.Vcube (Fintype.card E))) -
      (∫ V, D V ∂(GrandCoupling.Vcube (Fintype.card E)))
    rw [integral_sub' ((hA.add hB).sub hC) hD]
    rw [integral_sub' (hA.add hB) hC]
    rw [integral_add' hA hB]
  rw [hEq]
  have hcross₁ := causal_fkg_cross_fiber hpos hmono S.leftOrder S.rightOrder
    base σ hf hfC e U
  have hcross₂ := causal_fkg_cross_fiber hpos hmono S.rightOrder S.leftOrder
    base σ hf hfC e U
  dsimp only [Yl, Yr] at hcross₁ hcross₂ ⊢
  linarith


theorem realized_step_fiber_le {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ)
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) {Cf : ℝ}
    (hfC : ∀ ω, |f ω| ≤ Cf) (t : ℕ) (ht : 1 ≤ t)
    (htn : t - 1 < Fintype.card E) (U : Fin (Fintype.card E) → ℝ) :
    fiberAbsStep μ (realizedEquiv S base) f U t
      ≤ fiberObservable μ (realizedEquiv S base)
          (fun ω => f ω * Lindeberg.coord
            ((realizedEquiv S base : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩) ω)
          U (t - 1)
        + fiberObservable μ (realizedEquiv S base)
          (fun ω => f ω * Lindeberg.coord
            ((realizedEquiv S base : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩) ω)
          U t
        - fiberObservable μ (realizedEquiv S base) f U (t - 1)
            * fiberObservable μ (realizedEquiv S base)
              (Lindeberg.coord
                ((realizedEquiv S base : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩)) U t
        - fiberObservable μ (realizedEquiv S base) f U t
            * fiberObservable μ (realizedEquiv S base)
              (Lindeberg.coord
                ((realizedEquiv S base : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩))
              U (t - 1) := by
  unfold fiberAbsStep fiberObservable
  exact AdaptiveTau.step_fiber_le hpos hmono (realizedEquiv S base) hf hfC t ht htn U

end AdaptiveCausalKernel
end OSSS
end StatMech
