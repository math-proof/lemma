/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.OptionalStopping.Part3
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


lemma tsm_map_restrict_congr {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (S : Set α) {h h' : α → β} (hh : Measurable h) (hh' : Measurable h')
    (hagree : ∀ x ∈ S, h x = h' x) :
    Measure.map h (μ.restrict S) = Measure.map h' (μ.restrict S) := by
  ext T hT
  rw [Measure.map_apply hh hT, Measure.map_apply hh' hT,
      Measure.restrict_apply (hh hT), Measure.restrict_apply (hh' hT)]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor <;> rintro ⟨hx, hxs⟩ <;> refine ⟨?_, hxs⟩
  · rwa [← hagree x hxs]
  · rwa [hagree x hxs]


theorem tsm_measurePreserving_of_partition {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} {S : ℕ → Set α}
    (hSmeas : ∀ k, MeasurableSet (S k)) (hSdisj : Pairwise (Function.onFun Disjoint S))
    (hScover : ⋃ k, S k = Set.univ) {h : α → β} (hh : Measurable h) {hk : ℕ → α → β}
    (hhk : ∀ k, Measurable (hk k)) (hagree : ∀ k, ∀ x ∈ S k, h x = hk k x)
    (hsum : (Measure.sum (fun k => Measure.map (hk k) (μ.restrict (S k)))) = ν) :
    MeasurePreserving h μ ν := by
  refine ⟨hh, ?_⟩
  
  have hμsum : μ = Measure.sum (fun k => μ.restrict (S k)) := by
    conv_lhs => rw [← Measure.restrict_univ (μ := μ), ← hScover]
    exact Measure.restrict_iUnion hSdisj hSmeas
  rw [hμsum, Measure.map_sum hh.aemeasurable, ← hsum]
  congr 1
  funext k
  exact tsm_map_restrict_congr μ (S k) hh (hhk k) (hagree k)


lemma tsm_measurable_selRand (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (atl_selRand μ σ f t s A) := by
  have hpair : Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      (acp_join t A p.1, p.2)) :=
    Measurable.prodMk
      ((ubfSplit n t).symm.measurable.comp (measurable_const.prodMk measurable_fst))
      measurable_snd
  have hstop : Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      stopVal μ σ f (acp_join t A p.1)) :=
    (measurable_stopVal μ σ f).comp
      ((ubfSplit n t).symm.measurable.comp (measurable_const.prodMk measurable_fst))
  have key : ∀ m : ℕ, Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      adaptWt (acp_join t A p.1) p.2 m s) :=
    fun m => (measurable_adaptWt_fixed m s).comp hpair
  have hglue : Measurable (fun mp : ℕ × (({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ)) =>
      adaptWt (acp_join t A mp.2.1) mp.2.2 mp.1 s) :=
    measurable_from_prod_countable_right key
  exact hglue.comp (hstop.prodMk measurable_id)


end AdaptDisintegration
end OSSS
end StatMech
