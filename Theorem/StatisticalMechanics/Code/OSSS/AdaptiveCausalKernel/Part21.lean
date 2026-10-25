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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part21
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


theorem tripleLabelCube_frozenCrossRawAtom (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    tripleLabelCube (Fintype.card E) (frozenCrossRawAtom μ S base left right) =
      ∏ i : Fin (Fintype.card E),
        (((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))).prod
            (volume.restrict (Set.Icc (0 : ℝ) 1)))
          (crossRawTriple μ S base left right i) := by
  rw [tripleLabelCube, frozenCrossRawAtom, Measure.pi_pi]

lemma crossRawTriple_toReal_eq_crossTripleWeight
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) (i : Fin (Fintype.card E)) :
    let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
    ((ν.prod ν).prod ν (crossRawTriple μ S base left right i)).toReal =
      crossTripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i))
        (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i)
        (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i)
        (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i)
        (base (realizedEquiv S.leftOrder base i))
        (left (realizedEquiv S.leftOrder base i))
        (right (realizedEquiv S.leftOrder base i)) := by
  dsimp only
  let σ := realizedEquiv S.leftOrder base
  have hsigma : realizedEquiv S.leftOrder base = σ := rfl
  unfold crossRawTriple
  simp only [hsigma]
  cases hm : tripleModeAt S base (σ i) with
  | before =>
      simp only [hm, crossTripleWeight]
      rw [Measure.prod_prod, Measure.prod_prod, ENNReal.toReal_mul,
        ENNReal.toReal_mul, rawInterval_toReal_eq_bitWeight μ hpos,
        rawInterval_toReal_eq_bitWeight μ hpos,
        rawInterval_toReal_eq_bitWeight μ hpos]
  | flip =>
      simp only [hm, crossTripleWeight]
      rw [Measure.prod_prod, Measure.prod_prod, ENNReal.toReal_mul,
        ENNReal.toReal_mul, rawInterval_inter_toReal_eq_overlapWeight μ hpos,
        rawInterval_toReal_eq_bitWeight μ hpos]
      simp
  | after =>
      simp only [hm, crossTripleWeight, tripleOverlapWeight]
      rw [Measure.prod_prod, Measure.prod_prod, ENNReal.toReal_mul,
        ENNReal.toReal_mul,
        rawInterval_tripleInter_toReal_eq_tripleOverlapWeight μ hpos]
      simp

lemma overlapWeight_sum_target (a q : ℝ) (base : Bool) :
    overlapWeight a q base false + overlapWeight a q base true = bitWeight a base := by
  rw [overlapWeight_comm a q base false, overlapWeight_comm a q base true,
    overlapWeight_sum_base]
  cases base <;> simp [bitWeight]

lemma crossTripleWeight_sum_third (mode : TripleMode) (a q r : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b y : Bool) :
    crossTripleWeight mode a q r b y false +
        crossTripleWeight mode a q r b y true =
      splitWeight mode.leftIndependent a q b y := by
  cases mode with
  | before =>
      simp only [crossTripleWeight, TripleMode.leftIndependent, splitWeight, if_true]
      rw [← mul_add, bitWeight_false_add_true, mul_one]
      rfl
  | flip =>
      simp only [crossTripleWeight, TripleMode.leftIndependent, Bool.false_eq_true,
        splitWeight, if_false]
      rw [← mul_add, bitWeight_false_add_true, mul_one]
  | after =>
      simp only [crossTripleWeight, TripleMode.leftIndependent, Bool.false_eq_true,
        splitWeight, if_false]
      exact tripleOverlapWeight_sum_third a q r ha0 ha1 hq0 hq1 hr0 hr1 b y

lemma crossTripleWeight_sum_second (mode : TripleMode) (a q r : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b z : Bool) :
    crossTripleWeight mode a q r b false z +
        crossTripleWeight mode a q r b true z =
      splitWeight mode.rightIndependent a r b z := by
  cases mode with
  | before =>
      simp only [crossTripleWeight, TripleMode.rightIndependent, splitWeight, if_true]
      rw [show bitWeight a b * bitWeight q false * bitWeight r z +
          bitWeight a b * bitWeight q true * bitWeight r z =
        bitWeight a b * (bitWeight q false + bitWeight q true) * bitWeight r z by ring]
      rw [bitWeight_false_add_true, mul_one]
      rfl
  | flip =>
      simp only [crossTripleWeight, TripleMode.rightIndependent, splitWeight, if_true]
      rw [← add_mul, overlapWeight_sum_target]
      rfl
  | after =>
      simp only [crossTripleWeight, TripleMode.rightIndependent, Bool.false_eq_true,
        splitWeight, if_false]
      exact tripleOverlapWeight_sum_second a q r ha0 ha1 hq0 hq1 hr0 hr1 b z


end AdaptiveCausalKernel
end OSSS
end StatMech
