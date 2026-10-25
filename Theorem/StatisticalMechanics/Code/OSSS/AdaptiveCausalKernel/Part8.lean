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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part8
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


lemma tripleModeAt_beforeOfCausal_ne_flip {R : Finset E}
    (S : CausalOrder R) (base : ConfigSpace E) (z : E) :
    tripleModeAt (TripleOrder.beforeOfCausal S) base z ≠ .flip := by
  induction S with
  | done => simp [TripleOrder.beforeOfCausal, tripleModeAt]
  | node e he independent closed opened ihc iho =>
      simp only [TripleOrder.beforeOfCausal, tripleModeAt]
      by_cases hze : z = e
      · simp [hze]
      · simp only [hze, if_false]
        split <;> assumption

lemma tripleModeAt_extendDecisionTreeTriple_none_ne_flip
    (T : DecisionTree E) (known base : ConfigSpace E) (R : Finset E) (z : E) :
    tripleModeAt (extendDecisionTreeTriple none T known R) base z ≠ .flip := by
  induction T generalizing known R with
  | leaf b =>
      exact tripleModeAt_beforeOfCausal_ne_flip (fixedOrder R) base z
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeTriple]
      by_cases he : e ∈ R
      · simp only [he, dif_pos, tripleModeAt]
        by_cases hze : z = e
        · simp [hze]
        · simp only [hze, if_false]
          by_cases hb : base e
          · simp only [hb, if_true]
            exact iho (Function.update known e true) (R.erase e)
          · simp only [hb, Bool.false_eq_true, if_false]
            exact ihc (Function.update known e false) (R.erase e)
      · simp only [he, dif_neg]
        by_cases hb : known e
        · simp only [hb, if_true]
          exact iho known R
        · simp only [hb, Bool.false_eq_true, if_false]
          exact ihc known R

theorem tripleModeAt_extendDecisionTreeTriple_flip_unique
    (t : ℕ) (T : DecisionTree E) (known base : ConfigSpace E)
    (R : Finset E) (x y : E)
    (hx : tripleModeAt (extendDecisionTreeTriple (some t) T known R) base x = .flip)
    (hy : tripleModeAt (extendDecisionTreeTriple (some t) T known R) base y = .flip) :
    x = y := by
  induction T generalizing t known R with
  | leaf b =>
      exact False.elim
        (tripleModeAt_beforeOfCausal_ne_flip (fixedOrder R) base x hx)
  | node q opened closed iho ihc =>
      by_cases hqR : q ∈ R
      · rw [extendDecisionTreeTriple, dif_pos hqR] at hx hy
        cases t with
        | zero =>
            have eq_q (z : E)
                (hz : tripleModeAt
                  (.node q hqR .flip
                    (extendDecisionTreeTriple none closed
                      (Function.update known q false) (R.erase q))
                    (extendDecisionTreeTriple none opened
                      (Function.update known q true) (R.erase q))) base z = .flip) :
                z = q := by
              by_contra hn
              simp only [tripleModeAt, hn, if_false] at hz
              by_cases hb : base q
              · simp only [hb, if_true] at hz
                exact tripleModeAt_extendDecisionTreeTriple_none_ne_flip
                  opened (Function.update known q true) base (R.erase q) z hz
              · simp only [hb, Bool.false_eq_true, if_false] at hz
                exact tripleModeAt_extendDecisionTreeTriple_none_ne_flip
                  closed (Function.update known q false) base (R.erase q) z hz
            exact (eq_q x hx).trans (eq_q y hy).symm
        | succ t =>
            have hxn : x ≠ q := by
              intro h
              subst x
              simp [tripleModeAt] at hx
            have hyn : y ≠ q := by
              intro h
              subst y
              simp [tripleModeAt] at hy
            simp only [tripleModeAt, hxn, hyn, if_false] at hx hy
            by_cases hb : base q
            · simp only [hb, if_true] at hx hy
              exact iho t (Function.update known q true) (R.erase q) hx hy
            · simp only [hb, Bool.false_eq_true, if_false] at hx hy
              exact ihc t (Function.update known q false) (R.erase q) hx hy
      · rw [extendDecisionTreeTriple, dif_neg hqR] at hx hy
        by_cases hb : known q
        · simp only [hb, if_true] at hx hy
          exact iho t known R hx hy
        · simp only [hb, Bool.false_eq_true, if_false] at hx hy
          exact ihc t known R hx hy

theorem causal_abs_eq_four_terms { μ : ConfigSpace E → ℝ }
    (hpos : ∀ ω, 0 < μ ω) (hmono : IsMonotonicMeasure μ)
    {f : ConfigSpace E → ℝ} (hf : Monotone f)
    (t : ℕ) (T : DecisionTree E) (base : ConfigSpace E)
    (U V : Fin (Fintype.card E) → ℝ) (e : E)
    (he : tripleModeAt
      (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) base e = .flip) :
    let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
    let σ := realizedEquiv S.leftOrder base
    let Yl := codeMap μ (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.leftOrder base U V)
    let Yr := codeMap μ (σ : Fin (Fintype.card E) → E)
      (causalMixLabels S.rightOrder base U V)
    |f Yr - f Yl| =
      f Yl * Lindeberg.coord e Yl + f Yr * Lindeberg.coord e Yr -
        f Yl * Lindeberg.coord e Yr - f Yr * Lindeberg.coord e Yl := by
  dsimp only
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
  let σ := realizedEquiv S.leftOrder base
  let k : Fin (Fintype.card E) := σ.symm e
  let L := causalMixLabels S.leftOrder base U V
  let R := causalMixLabels S.rightOrder base U V
  let Yl := codeMap μ (σ : Fin (Fintype.card E) → E) L
  let Yr := codeMap μ (σ : Fin (Fintype.card E) → E) R
  have hke : σ k = e := by simp [k]
  have hσ : realizedEquiv S.rightOrder base = σ := by
    exact (realizedEquiv_leftOrder_eq_rightOrder S base).symm
  have hoff : ∀ i : Fin (Fintype.card E), (i : ℕ) ≠ k → L i = R i := by
    intro i hi
    have hie : σ i ≠ e := by
      intro h
      have : i = k := σ.injective (by simpa [k] using h)
      exact hi (congrArg Fin.val this)
    apply causalMixLabels_left_eq_right_of_mode_ne_flip
    intro hm
    have := tripleModeAt_extendDecisionTreeTriple_flip_unique
      t T base base Finset.univ (σ i) e hm he
    exact hie this
  have hkL : L k = U k := by
    dsimp only [L]
    rw [causalMixLabels_leftOrder_apply]
    rw [hke, he]
  have hkR : R k = V k := by
    dsimp only [R]
    rw [causalMixLabels_rightOrder_apply]
    rw [hσ]
    rw [hke, he]
  have hdet : Lindeberg.coord e Yr = Lindeberg.coord e Yl → Yr = Yl := by
    intro hc
    have hbit : Yr e = Yl e := by
      unfold Lindeberg.coord at hc
      by_cases h1 : Yr e <;> by_cases h2 : Yl e <;> simp_all
    apply GrandCouplingAssembly.codeMap_det μ
      (σ : Fin (Fintype.card E) → E) σ.injective R L
      k k.2 (fun i hi => (hoff i hi).symm)
    simpa [hke] using hbit
  have hcmp : (f Yl ≤ f Yr ∧ Lindeberg.coord e Yl ≤ Lindeberg.coord e Yr) ∨
      (f Yr ≤ f Yl ∧ Lindeberg.coord e Yr ≤ Lindeberg.coord e Yl) := by
    rcases le_total (U k) (V k) with huv | hvu
    · left
      have hlr : L ≤ R := by
        intro i
        by_cases hi : (i : ℕ) = k
        · have hik : i = k := Fin.ext hi
          subst i
          rw [hkL, hkR]
          exact huv
        · rw [hoff i hi]
      have hy : Yl ≤ Yr := GrandCoupling.codeMap_mono_u hpos hmono _ hlr
      exact ⟨hf hy, Lindeberg.coord_mono e hy⟩
    · right
      have hrl : R ≤ L := by
        intro i
        by_cases hi : (i : ℕ) = k
        · have hik : i = k := Fin.ext hi
          subst i
          rw [hkL, hkR]
          exact hvu
        · rw [hoff i hi]
      have hy : Yr ≤ Yl := GrandCoupling.codeMap_mono_u hpos hmono _ hrl
      exact ⟨hf hy, Lindeberg.coord_mono e hy⟩
  exact GrandCouplingAssembly.tt_algebra (f Yr) (f Yl)
    (Lindeberg.coord e Yr) (Lindeberg.coord e Yl)
    (GrandCouplingAssembly.coord_eq01 e Yr)
    (GrandCouplingAssembly.coord_eq01 e Yl) hcmp (fun h => by rw [hdet h])


end AdaptiveCausalKernel
end OSSS
end StatMech
