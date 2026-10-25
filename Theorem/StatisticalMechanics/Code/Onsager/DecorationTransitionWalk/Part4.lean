/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part6
import Def.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part3


namespace StatMech.Onsager

open Finset SimpleGraph

@[simp] theorem ons_decTransitionWalk_edges_toFinset
    (L : ℕ) (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    (ons_decTransitionWalk L d₂ d₁ hstep).edges.toFinset =
      insert s(d₁, ons_dartRev L d₁)
        (ons_decChainPathEdges d₂.1 (d₁.2 + 2) d₂.2) := by
  have hstart : (d₂.1, d₁.2 + 2) = ons_dartRev L d₁ := by
    apply Prod.ext
    · exact hstep.trans (ons_dartRev_fst_eq_step L d₁).symm
    · simp [ons_dartRev]
  simp [ons_decTransitionWalk]
  rw [hstart]

theorem ons_decChainEdge_injective
    {L : ℕ} (site : ZMod L × ZMod L) :
    Function.Injective (ons_decChainEdge site) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [ons_decChainEdge, Sym2.eq_iff, Fin.ext_iff] at hij ⊢

theorem ons_externalEdge_not_mem_chainPath
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (site : ZMod L × ZMod L) (a b : Fin 4) :
    s(d, ons_dartRev L d) ∉ ons_decChainPathEdges site a b := by
  intro hmem
  rw [ons_decChainPathEdges, Finset.mem_image] at hmem
  obtain ⟨i, hi, hedge⟩ := hmem
  apply ons_decChainEdge_not_external L site i
  exact ⟨d, hedge⟩

theorem ons_decTransitionWalk_isTrail
    (L : ℕ) [Fact (2 < L)] (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    (ons_decTransitionWalk L d₂ d₁ hstep).IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def]
  have hchain :=
    (ons_decPortChainPath_isPath L d₂.1 (d₁.2 + 2) d₂.2).isTrail
  rw [SimpleGraph.Walk.isTrail_def] at hchain
  simp [ons_decTransitionWalk, hchain]
  intro hedge
  apply ons_externalEdge_not_mem_chainPath
    L d₁ d₂.1 (d₁.2 + 2) d₂.2
  rw [← ons_decPortChainPath_edges_toFinset]
  apply List.mem_toFinset.mpr
  simpa [hstep, ons_dartRev] using hedge


theorem ons_decTransitionExponent_eq_walkEdges
    (L : ℕ) [Fact (2 < L)] (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    ons_decTransitionExponent L d₂ d₁ =
      ons_finsetExponent
        (ons_decTransitionWalk L d₂ d₁ hstep).edges.toFinset := by
  rw [ons_decTransitionWalk_edges_toFinset]
  unfold ons_decTransitionExponent ons_decChainPathEdges
  rw [ons_finsetExponent_insert]
  · rw [ons_finsetExponent_image
      (ons_decChainPathIndices (d₁.2 + 2) d₂.2)
      (ons_decChainEdge d₂.1)
      (ons_decChainEdge_injective d₂.1).injOn]
  · exact ons_externalEdge_not_mem_chainPath L d₁ d₂.1
      (d₁.2 + 2) d₂.2

theorem ons_decTransitionExponent_prod
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    (ons_decTransitionExponent L d₂ d₁).prod
        (fun edge n ↦ decWeight edge ^ n) =
      ons_decTransitionWeight L decWeight d₂ d₁ := by
  rw [ons_decTransitionExponent_eq_walkEdges L d₂ d₁ hstep,
    ons_finsetExponent_prod,
    ons_decTransitionWalk_edges_toFinset,
    Finset.prod_insert
      (ons_externalEdge_not_mem_chainPath L d₁ d₂.1
        (d₁.2 + 2) d₂.2)]
  unfold ons_decChainPathEdges ons_decTransitionWeight
  rw [Finset.prod_image (ons_decChainEdge_injective d₂.1).injOn]

theorem ons_KWmatDecorationWeightedPhase_entry_factor
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (omega u v : ℂ)
    (d₂ d₁ : ons_Dart L) :
    ons_KWmatDecorationWeightedPhase L decWeight omega u v d₂ d₁ =
      ons_decTransitionScalar L omega u v d₂ d₁ *
        (ons_decTransitionExponent L d₂ d₁).prod
          (fun edge n ↦ decWeight edge ^ n) := by
  by_cases hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1
  · rw [ons_decTransitionExponent_prod L decWeight d₂ d₁ hstep]
    simp [ons_KWmatDecorationWeightedPhase, ons_decTransitionScalar, hstep]
    ring
  · simp [ons_KWmatDecorationWeightedPhase,
      ons_decTransitionScalar, hstep]

theorem ons_finsuppProd_sum_pow
    {I E R : Type*} [Fintype I] [DecidableEq E] [CommMonoid R]
    (m : I → E →₀ ℕ) (weight : E → R) :
    (∑ i, m i).prod (fun edge n ↦ weight edge ^ n) =
      ∏ i, (m i).prod (fun edge n ↦ weight edge ^ n) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        Finsupp.prod_add_index]
      · rw [ih]
      · intro edge hedge
        simp
      · intro edge hedge n₁ n₂
        simp [pow_add]

theorem ons_loopWeight_KWmatDecorationWeightedPhase
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (decWeight : ons_DecEdge L → ℂ) (omega u v : ℂ)
    (d : Fin n → ons_Dart L) :
    ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d =
      ons_decLoopScalar L omega u v d *
        (ons_decLoopExponent L d).prod
          (fun edge k ↦ decWeight edge ^ k) := by
  unfold ons_loopWeight ons_decLoopScalar ons_decLoopExponent
  simp_rw [ons_KWmatDecorationWeightedPhase_entry_factor]
  rw [Finset.prod_mul_distrib, ons_finsuppProd_sum_pow]

end StatMech.Onsager
