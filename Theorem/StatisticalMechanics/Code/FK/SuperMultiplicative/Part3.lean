/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FK.FeketeLimit
import Def.StatisticalMechanics.Code.FK.SuperMultiplicative.Part2
open scoped BigOperators
open SimpleGraph Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

section Combine

variable {V W : Type*}


@[simp] theorem fsm_combine_inl (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) (a b : V) :
    fsm_combine σ τ s(Sum.inl a, Sum.inl b) = σ s(a, b) := rfl

@[simp] theorem fsm_combine_inr (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) (a b : W) :
    fsm_combine σ τ s(Sum.inr a, Sum.inr b) = τ s(a, b) := rfl

theorem fsm_combine_map_inl (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) (e : Sym2 V) :
    fsm_combine σ τ (Sym2.map Sum.inl e) = σ e := by
  induction e using Sym2.ind with | _ a b => simp [Sym2.map_mk]

theorem fsm_combine_map_inr (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) (e : Sym2 W) :
    fsm_combine σ τ (Sym2.map Sum.inr e) = τ e := by
  induction e using Sym2.ind with | _ a b => simp [Sym2.map_mk]


theorem fsm_combine_injective :
    Function.Injective fun p : (Sym2 V → Bool) × (Sym2 W → Bool) => fsm_combine p.1 p.2 := by
  rintro ⟨σ₁, τ₁⟩ ⟨σ₂, τ₂⟩ h
  simp only at h
  ext1
  · funext e; show σ₁ e = σ₂ e
    rw [← fsm_combine_map_inl σ₁ τ₁ e, ← fsm_combine_map_inl σ₂ τ₂ e, h]
  · funext e; show τ₁ e = τ₂ e
    rw [← fsm_combine_map_inr σ₁ τ₁ e, ← fsm_combine_map_inr σ₂ τ₂ e, h]

end Combine


section Weight

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]


theorem fsm_edgeProduct_combine (p : ℝ) (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    edgeProduct (G ⊕g H) p (fsm_combine σ τ) = edgeProduct G p σ * edgeProduct H p τ := by
  unfold edgeProduct
  rw [fsm_edgeFinset_sum, Finset.prod_union (fsm_images_disjoint G H)]
  congr 1
  · rw [Finset.prod_image (fun x _ y _ h => fsm_map_inl_injective h)]
    exact Finset.prod_congr rfl fun e _ => by rw [fsm_combine_map_inl]
  · rw [Finset.prod_image (fun x _ y _ h => fsm_map_inr_injective h)]
    exact Finset.prod_congr rfl fun e _ => by rw [fsm_combine_map_inr]


theorem fsm_openSub_combine (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    openSub (G ⊕g H) (fsm_combine σ τ) = (openSub G σ) ⊕g (openSub H τ) := by
  ext x y
  match x, y with
  | Sum.inl a, Sum.inl b => simp only [openSub_adj, SimpleGraph.sum_adj, fsm_combine_inl]
  | Sum.inr c, Sum.inr d => simp only [openSub_adj, SimpleGraph.sum_adj, fsm_combine_inr]
  | Sum.inl a, Sum.inr d => simp [openSub_adj, SimpleGraph.sum_adj]
  | Sum.inr c, Sum.inl b => simp [openSub_adj, SimpleGraph.sum_adj]


theorem fsm_numClusters_combine (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    numClusters (G ⊕g H) (fsm_combine σ τ)
      = numClusters G σ + numClusters H τ := by
  classical
  unfold numClusters
  
  rw [Nat.card_eq_fintype_card.symm, Nat.card_eq_fintype_card.symm, Nat.card_eq_fintype_card.symm]
  rw [show (openSub (G ⊕g H) (fsm_combine σ τ)) = (openSub G σ) ⊕g (openSub H τ) from
        fsm_openSub_combine G H σ τ]
  rw [Nat.card_congr (fsm_ccSumEquiv (openSub G σ) (openSub H τ)), Nat.card_sum]


theorem fsm_fkWeight_combine (p q : ℝ) (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    fkWeight (G ⊕g H) p q (fsm_combine σ τ) = fkWeight G p q σ * fkWeight H p q τ := by
  unfold fkWeight
  rw [fsm_edgeProduct_combine G H p σ τ, fsm_numClusters_combine G H σ τ, pow_add]
  ring

end Weight


section Super

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]


theorem fsm_fkZ_sum_ge {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkZ G p q * fkZ H p q ≤ fkZ (G ⊕g H) p q := by
  classical
  
  have hprod : fkZ G p q * fkZ H p q
      = ∑ στ : (Sym2 V → Bool) × (Sym2 W → Bool),
          fkWeight (G ⊕g H) p q (fsm_combine στ.1 στ.2) := by
    unfold fkZ
    rw [Fintype.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ =>
      (fsm_fkWeight_combine G H p q σ τ).symm
  rw [hprod]
  
  have himg : (∑ στ : (Sym2 V → Bool) × (Sym2 W → Bool),
          fkWeight (G ⊕g H) p q (fsm_combine στ.1 στ.2))
      = ∑ ω ∈ Finset.univ.image (fun στ : (Sym2 V → Bool) × (Sym2 W → Bool) =>
            fsm_combine στ.1 στ.2), fkWeight (G ⊕g H) p q ω := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact fsm_combine_injective h
  rw [himg]
  
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
  intro ω _ _
  exact fkWeight_nonneg (G ⊕g H) hp hp1 hq ω


theorem fsm_neglog_sum_le {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    - Real.log (fkZ (G ⊕g H) p q)
      ≤ - Real.log (fkZ G p q) + - Real.log (fkZ H p q) := by
  have hZG : 0 < fkZ G p q := fkZ_pos G hp hp1 hq
  have hZH : 0 < fkZ H p q := fkZ_pos H hp hp1 hq
  have hge : fkZ G p q * fkZ H p q ≤ fkZ (G ⊕g H) p q := fsm_fkZ_sum_ge G H hp hp1 hq
  have hlog : Real.log (fkZ G p q) + Real.log (fkZ H p q)
      ≤ Real.log (fkZ (G ⊕g H) p q) := by
    rw [← Real.log_mul hZG.ne' hZH.ne']
    exact Real.log_le_log (mul_pos hZG hZH) hge
  linarith

end Super
end FK
end StatMech
