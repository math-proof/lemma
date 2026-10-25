/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.UBlockFactor
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma acp_detAtC_congr_of_codeMap_agree {n : ℕ} (σ : Fin n → E) (f : ConfigSpace E → ℝ)
    (X X' : ConfigSpace E) (m : ℕ)
    (hpref : ∀ e ∈ prefixSet σ m, X e = X' e) :
    detAtC σ f X m ↔ detAtC σ f X' m := by
  have hfXX' : detAtC σ f X m → f X = f X' := fun hdet =>
    (hdet X' (fun e he => (hpref e he).symm)).symm
  unfold detAtC
  constructor
  · intro hdet w hw
    have hwX : ∀ e ∈ prefixSet σ m, w e = X e := fun e he => by rw [hw e he, ← hpref e he]
    rw [hdet w hwX]; exact hfXX' hdet
  · intro hdet w hw
    have hfX'X : f X' = f X := by
      have hdet' : detAtC σ f X' m := hdet
      exact (hdet' X (fun e he => hpref e he)).symm
    have hwX' : ∀ e ∈ prefixSet σ m, w e = X' e := fun e he => by rw [hw e he, hpref e he]
    rw [hdet w hwX']; exact hfX'X


lemma acp_stopVal_gt_congr (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U U' : Fin n → ℝ) (t : ℕ)
    (hagree : ∀ i : Fin n, (i : ℕ) < t → U i = U' i) :
    (t + 1 ≤ stopVal μ σ f U) ↔ (t + 1 ≤ stopVal μ σ f U') := by
  unfold stopVal stopValC
  rw [Nat.le_find_iff, Nat.le_find_iff]
  constructor <;> intro h m hm <;> rw [Nat.lt_succ_iff] at hm
  · intro hdet'
    refine h m (by omega) ?_
    refine (acp_detAtC_congr_of_codeMap_agree (σ : Fin n → E) f _ _ m ?_).mpr hdet'
    exact codeMap_agree_on_prefix μ σ U U' m (fun i hi => hagree i (by omega))
  · intro hdet
    refine h m (by omega) ?_
    refine (acp_detAtC_congr_of_codeMap_agree (σ : Fin n → E) f _ _ m ?_).mpr hdet
    exact codeMap_agree_on_prefix μ σ U' U m (fun i hi => (hagree i (by omega)).symm)


end AdaptDisintegration
end OSSS
end StatMech
