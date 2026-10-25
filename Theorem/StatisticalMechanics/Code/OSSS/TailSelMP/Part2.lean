/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.OptionalStopping.Part3
import Def.StatisticalMechanics.Code.OSSS.TailSelMP
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma tsm_measurable_switch (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
        stopVal μ σ f (acp_join t A p.1)) := by
  have hjoin : Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      acp_join t A p.1) :=
    (ubfSplit n t).symm.measurable.comp (measurable_const.prodMk measurable_fst)
  exact (measurable_stopVal μ σ f).comp hjoin


lemma tsm_switchPiece_meas (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (k : ℕ) :
    MeasurableSet (tsm_switchPiece μ σ f t A k) :=
  (tsm_measurable_switch μ σ f t A) (measurableSet_singleton k)


lemma tsm_switchPiece_disj (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Pairwise (Function.onFun Disjoint (tsm_switchPiece μ σ f t A)) := by
  intro k l hkl
  refine Set.disjoint_left.mpr ?_
  intro p hpk hpl
  exact hkl (by rw [← (show stopVal μ σ f (acp_join t A p.1) = k from hpk),
    (show stopVal μ σ f (acp_join t A p.1) = l from hpl)])


lemma tsm_switchPiece_cover (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    ⋃ k, tsm_switchPiece μ σ f t A k = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨stopVal μ σ f (acp_join t A p.1), rfl⟩


lemma tsm_selRand_eq_on_piece (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (k : ℕ)
    (p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ))
    (hp : p ∈ tsm_switchPiece μ σ f t A k) :
    atl_selRand μ σ f t s A p = osp_tailSelFixed t s k A p := by
  show adaptWt (acp_join t A p.1) p.2 (stopVal μ σ f (acp_join t A p.1)) s
      = adaptWt (acp_join t A p.1) p.2 k s
  rw [show stopVal μ σ f (acp_join t A p.1) = k from hp]


end AdaptDisintegration
end OSSS
end StatMech
