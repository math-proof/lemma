/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewriteDichotomy.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyDischarge
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Def.StatisticalMechanics.Code.Sharpness.HcovAssembly.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

namespace HcovAssembly

open StatMech.Sharpness (ofEdgeFun weight currentSum)

open StatMech.Sharpness.FluxEdgeCopy (Copy endsM endsM_not_isDiag sourcePairDisconnSum
  sourcePairDisconnSum_eq_switching_gap)

open StatMech.Sharpness.RandomCurrent (connK switching_disconnect_card)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (H : SimpleGraph V) [DecidableRel H.Adj]


theorem hca_gap_mul_weight_eq (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (u v : V)
    (m : ↥H.edgeFinset → ℕ) :
    hca_gap H m A u v * weight H β J (ofEdgeFun H m)
      = (∑ S : Finset (Copy H m),
            (if RandomCurrent.sources (endsM H m) S = A then (1 : ℝ) else 0)
              * (if RandomCurrent.sources (endsM H m) (univ \ S) = (∅ : Finset V) then 1 else 0))
          * weight H β J (ofEdgeFun H m)
        - (∑ S : Finset (Copy H m),
            (if RandomCurrent.sources (endsM H m) S = A ∆ {u, v} then (1 : ℝ) else 0)
              * (if RandomCurrent.sources (endsM H m) (univ \ S) = ({u, v} : Finset V) then 1 else 0))
          * weight H β J (ofEdgeFun H m) := by
  classical
  rw [GhostCurrentRep.gcr_pairCount_empty H m A,
    GhostCurrentRep.gcr_pairCount_pair H m A u v]
  unfold hca_gap
  by_cases hAm : RandomCurrent.sources (endsM H m) univ = A
  · simp only [if_pos hAm, one_mul]; ring
  · simp only [if_neg hAm, zero_mul]; ring


theorem hca_summable_gap (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (u v : V) :
    Summable (fun m : ↥H.edgeFinset → ℕ =>
      hca_gap H m A u v * weight H β J (ofEdgeFun H m)) := by
  classical
  have hsum := (GhostCurrentRep.gcr_summable_edgecopy H β J A ∅).sub
    (GhostCurrentRep.gcr_summable_edgecopy H β J (A ∆ {u, v}) {u, v})
  refine hsum.congr (fun m => ?_)
  rw [hca_gap_mul_weight_eq H β J A u v m]


theorem hca_summable_pairSum (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (u v : V)
    (P : (↥H.edgeFinset → ℕ) → Prop) :
    Summable (fun m : ↥H.edgeFinset → ℕ =>
      (if P m then (1 : ℝ) else 0) * hca_gap H m A u v * weight H β J (ofEdgeFun H m)) := by
  classical
  refine Summable.of_norm ?_
  refine ((hca_summable_gap H β J A u v).norm).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun m => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases hP : P m
  · rw [if_pos hP, one_mul]
  · rw [if_neg hP, zero_mul, zero_mul, abs_zero]; positivity


theorem hca_pairSum_add (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (u v : V)
    (P₁ P₂ : (↥H.edgeFinset → ℕ) → Prop)
    (hdisj : ∀ m, ¬ (P₁ m ∧ P₂ m)) :
    hca_pairSum H β J A u v (fun m => P₁ m ∨ P₂ m)
      = hca_pairSum H β J A u v P₁ + hca_pairSum H β J A u v P₂ := by
  classical
  unfold hca_pairSum
  rw [← Summable.tsum_add (hca_summable_pairSum H β J A u v P₁)
    (hca_summable_pairSum H β J A u v P₂)]
  refine tsum_congr (fun m => ?_)
  by_cases h1 : P₁ m <;> by_cases h2 : P₂ m
  · exact absurd ⟨h1, h2⟩ (hdisj m)
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]


theorem hca_pairSum_disconn_eq (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) {u v : V} (huv : u ≠ v) :
    hca_pairSum H β J A u v (fun m => ¬ connK (endsM H m) univ u v)
      = sourcePairDisconnSum H β J A ∅ u v := by
  classical
  rw [sourcePairDisconnSum_eq_switching_gap H β J A u v huv]
  unfold hca_pairSum
  refine tsum_congr (fun m => ?_)
  simp only []
  
  congr 1
  
  rw [show (if RandomCurrent.sources (endsM H m) univ = A then
        ((#((univ : Finset (Copy H m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM H m) K = A)) : ℝ)
          - #((univ : Finset (Copy H m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM H m) K = A ∆ {u, v})))
       else 0) = hca_gap H m A u v from rfl]
  convert (hca_gap_disconn H m A huv).symm using 3


theorem hca_gap_srcGate (m : ↥H.edgeFinset → ℕ) (A : Finset V) (u v : V) :
    hca_gap H m A u v
      = (if RandomCurrent.sources (endsM H m) univ = A then (1 : ℝ) else 0) * hca_gap H m A u v := by
  classical
  by_cases hAm : RandomCurrent.sources (endsM H m) univ = A
  · rw [if_pos hAm, one_mul]
  · conv_lhs => unfold hca_gap
    rw [if_neg hAm, if_neg hAm, zero_mul]


theorem hca_pairSum_disconn_conj_eq (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) {u v : V} (huv : u ≠ v) :
    hca_pairSum H β J A u v
        (fun m => RandomCurrent.sources (endsM H m) univ = A ∧ ¬ connK (endsM H m) univ u v)
      = sourcePairDisconnSum H β J A ∅ u v := by
  classical
  rw [← hca_pairSum_disconn_eq H β J A huv]
  unfold hca_pairSum
  refine tsum_congr (fun m => ?_)
  by_cases hAm : RandomCurrent.sources (endsM H m) univ = A
  · 
    by_cases hC : connK (endsM H m) univ u v <;> simp [hAm, hC]
  · 
    have hg0 : hca_gap H m A u v = 0 := by unfold hca_gap; rw [if_neg hAm]
    rw [hg0]; ring


theorem hca_sourcePairDisconn_deltaRewrite (β : ℝ) (J : Sym2 V → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    sourcePairDisconnSum H β J ({o, x, y, g} : Finset V) ∅ o g
      = hca_pairSum H β J ({o, x, y, g} : Finset V) o g
          (fun m => (RandomCurrent.sources (endsM H m) univ = {o, x, y, g}
              ∧ ¬ connK (endsM H m) univ o g)
            ∧ (connK (endsM H m) univ o x ∧ connK (endsM H m) univ y g))
        + hca_pairSum H β J ({o, x, y, g} : Finset V) o g
            (fun m => (RandomCurrent.sources (endsM H m) univ = {o, x, y, g}
                ∧ ¬ connK (endsM H m) univ o g)
              ∧ (connK (endsM H m) univ o y ∧ connK (endsM H m) univ x g)) := by
  classical
  rw [← hca_pairSum_disconn_conj_eq H β J ({o, x, y, g} : Finset V) hog]
  refine sdr_deltaRewrite_perEdge
    (hca_pairSum H β J ({o, x, y, g} : Finset V) o g
      (fun m => RandomCurrent.sources (endsM H m) univ = {o, x, y, g} ∧ ¬ connK (endsM H m) univ o g))
    (hca_pairSum H β J ({o, x, y, g} : Finset V) o g)
    (fun P₁ P₂ _ _ _ hdisj => hca_pairSum_add H β J ({o, x, y, g} : Finset V) o g P₁ P₂ hdisj)
    (disconn := fun m =>
      RandomCurrent.sources (endsM H m) univ = {o, x, y, g} ∧ ¬ connK (endsM H m) univ o g)
    (caseA := fun m => connK (endsM H m) univ o x ∧ connK (endsM H m) univ y g)
    (caseB := fun m => connK (endsM H m) univ o y ∧ connK (endsM H m) univ x g)
    rfl ?_
  
  rintro m ⟨hsrc, hdisc⟩
  exact RandomCurrent.disconnect_dichotomy_prop (endsM H m) univ
    (fun i _ => endsM_not_isDiag H m i) hox hoy hog hxy hxg hyg hsrc hdisc


end HcovAssembly
end Sharpness
end StatMech
