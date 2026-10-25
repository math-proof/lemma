/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.BoxFeketeData.Part2
import Structure.StatisticalMechanics.Code.FK.FKInterfaceSubadd
open scoped BigOperators
open SimpleGraph Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false


namespace StatMech

namespace FK

section Interface

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
  (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]


variable {G H K}


theorem fis_combine_false_of_interface (hci : fis_CrossInterface G H K)
    (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) {e : Sym2 (V ⊕ W)}
    (he : e ∈ fis_interface G H K) : fsm_combine σ τ e = false := by
  classical
  rw [fis_interface, Finset.mem_sdiff, mem_edgeFinset, mem_edgeFinset] at he
  obtain ⟨hK, hnot⟩ := he
  
  
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_edgeSet] at hK hnot
    match x, y with
    | Sum.inl a, Sum.inl b =>
      exact absurd (show (G ⊕g H).Adj (Sum.inl a) (Sum.inl b) from hci.inl a b hK) hnot
    | Sum.inr c, Sum.inr d =>
      exact absurd (show (G ⊕g H).Adj (Sum.inr c) (Sum.inr d) from hci.inr c d hK) hnot
    | Sum.inl a, Sum.inr d => rfl
    | Sum.inr c, Sum.inl b => rfl


theorem fis_openSub_combine_eq (hci : fis_CrossInterface G H K)
    (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    openSub K (fsm_combine σ τ) = openSub (G ⊕g H) (fsm_combine σ τ) := by
  classical
  ext x y
  simp only [openSub_adj]
  constructor
  · rintro ⟨hKadj, hopen⟩
    
    have hmem : s(x, y) ∈ (G ⊕g H).edgeFinset := by
      by_contra hnot
      have hint : s(x, y) ∈ fis_interface G H K := by
        rw [fis_interface, Finset.mem_sdiff]
        exact ⟨by rw [mem_edgeFinset, mem_edgeSet]; exact hKadj, hnot⟩
      rw [fis_combine_false_of_interface hci σ τ hint] at hopen
      exact absurd hopen (by simp)
    refine ⟨?_, hopen⟩
    rw [mem_edgeFinset, mem_edgeSet] at hmem
    exact hmem
  · rintro ⟨hGHadj, hopen⟩
    exact ⟨hci.le hGHadj, hopen⟩


theorem fis_numClusters_combine (hci : fis_CrossInterface G H K)
    (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    numClusters K (fsm_combine σ τ) = numClusters G σ + numClusters H τ := by
  classical
  
  have hcc : numClusters K (fsm_combine σ τ) = numClusters (G ⊕g H) (fsm_combine σ τ) := by
    unfold numClusters
    rw [Nat.card_eq_fintype_card.symm, Nat.card_eq_fintype_card.symm]
    rw [fis_openSub_combine_eq hci σ τ]
  rw [hcc]
  exact fsm_numClusters_combine G H σ τ


theorem fis_sum_edgeFinset_subset (hci : fis_CrossInterface G H K) :
    (G ⊕g H).edgeFinset ⊆ K.edgeFinset :=
  edgeFinset_mono hci.le


theorem fis_edgeFinset_eq (hci : fis_CrossInterface G H K) :
    K.edgeFinset = (G ⊕g H).edgeFinset ∪ fis_interface G H K := by
  rw [fis_interface, Finset.union_sdiff_of_subset (fis_sum_edgeFinset_subset hci)]


theorem fis_edgeProduct_combine (hci : fis_CrossInterface G H K) (p : ℝ)
    (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    edgeProduct K p (fsm_combine σ τ)
      = (1 - p) ^ (fis_interface G H K).card * (edgeProduct G p σ * edgeProduct H p τ) := by
  classical
  have hdisj : Disjoint ((G ⊕g H).edgeFinset) (fis_interface G H K) := by
    rw [fis_interface]; exact Finset.disjoint_sdiff
  
  have hsplit : edgeProduct K p (fsm_combine σ τ)
      = (∏ e ∈ (G ⊕g H).edgeFinset, (if fsm_combine σ τ e then p else 1 - p))
        * (∏ e ∈ fis_interface G H K, (if fsm_combine σ τ e then p else 1 - p)) := by
    unfold edgeProduct
    rw [fis_edgeFinset_eq hci, Finset.prod_union hdisj]
  rw [hsplit]
  
  have hGH : (∏ e ∈ (G ⊕g H).edgeFinset, (if fsm_combine σ τ e then p else 1 - p))
      = edgeProduct G p σ * edgeProduct H p τ := by
    have : (∏ e ∈ (G ⊕g H).edgeFinset, (if fsm_combine σ τ e then p else 1 - p))
        = edgeProduct (G ⊕g H) p (fsm_combine σ τ) := rfl
    rw [this, fsm_edgeProduct_combine G H p σ τ]
  
  have hI : (∏ e ∈ fis_interface G H K, (if fsm_combine σ τ e then p else 1 - p))
      = (1 - p) ^ (fis_interface G H K).card := by
    rw [show (∏ e ∈ fis_interface G H K, (if fsm_combine σ τ e then p else 1 - p))
          = ∏ e ∈ fis_interface G H K, (1 - p) from
        Finset.prod_congr rfl (fun e he => by
          rw [fis_combine_false_of_interface hci σ τ he]; simp),
      Finset.prod_const]
  rw [hGH, hI]; ring


theorem fis_fkWeight_combine (hci : fis_CrossInterface G H K) (p q : ℝ)
    (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    fkWeight K p q (fsm_combine σ τ)
      = (1 - p) ^ (fis_interface G H K).card * (fkWeight G p q σ * fkWeight H p q τ) := by
  unfold fkWeight
  rw [fis_edgeProduct_combine hci p σ τ, fis_numClusters_combine hci σ τ, pow_add]
  ring


theorem fis_fkZ_interface_ge (hci : fis_CrossInterface G H K) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (1 - p) ^ (fis_interface G H K).card * (fkZ G p q * fkZ H p q) ≤ fkZ K p q := by
  classical
  
  
  have hprod : (1 - p) ^ (fis_interface G H K).card * (fkZ G p q * fkZ H p q)
      = ∑ στ : (Sym2 V → Bool) × (Sym2 W → Bool),
          fkWeight K p q (fsm_combine στ.1 στ.2) := by
    unfold fkZ
    rw [Fintype.sum_mul_sum, Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [fis_fkWeight_combine hci p q σ τ]
  rw [hprod]
  
  have himg : (∑ στ : (Sym2 V → Bool) × (Sym2 W → Bool),
          fkWeight K p q (fsm_combine στ.1 στ.2))
      = ∑ ω ∈ Finset.univ.image (fun στ : (Sym2 V → Bool) × (Sym2 W → Bool) =>
            fsm_combine στ.1 στ.2), fkWeight K p q ω := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact fsm_combine_injective h
  rw [himg]
  
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
  intro ω _ _
  exact fkWeight_nonneg K hp hp1 hq ω


theorem fis_neglog_interface_le (hci : fis_CrossInterface G H K) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    - Real.log (fkZ K p q)
      ≤ - Real.log (fkZ G p q) + - Real.log (fkZ H p q)
        - (fis_interface G H K).card * Real.log (1 - p) := by
  have hZG : 0 < fkZ G p q := fkZ_pos G hp hp1 hq
  have hZH : 0 < fkZ H p q := fkZ_pos H hp hp1 hq
  have hZK : 0 < fkZ K p q := fkZ_pos K hp hp1 hq
  have h1mp : (0:ℝ) < 1 - p := by linarith
  have hge : (1 - p) ^ (fis_interface G H K).card * (fkZ G p q * fkZ H p q) ≤ fkZ K p q :=
    fis_fkZ_interface_ge hci hp hp1 hq
  
  have hpos : 0 < (1 - p) ^ (fis_interface G H K).card * (fkZ G p q * fkZ H p q) :=
    mul_pos (pow_pos h1mp _) (mul_pos hZG hZH)
  have hlog : Real.log ((1 - p) ^ (fis_interface G H K).card * (fkZ G p q * fkZ H p q))
      ≤ Real.log (fkZ K p q) := Real.log_le_log hpos hge
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hZG.ne' hZH.ne',
    Real.log_pow] at hlog
  push_cast at hlog ⊢
  linarith

end Interface


theorem fis_subadditive_of_bounded {u : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ m n, u (m + n) ≤ u m + u n + C) :
    Subadditive (fun n => u n + C) := by
  intro m n
  simp only
  have := hu m n
  linarith


theorem fis_interfaceData_of_bounded {V : ℕ → Type*} [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)] (Gn : ∀ n, SimpleGraph (V n)) [∀ n, DecidableRel (Gn n).Adj]
    (q : ℝ) (t : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hglue : ∀ m n, - Real.log (fkZ (Gn (m + n)) (fsc_logistic t) q)
        ≤ - Real.log (fkZ (Gn m) (fsc_logistic t) q)
          + - Real.log (fkZ (Gn n) (fsc_logistic t) q) + C)
    (hbdd : BddBelow (Set.range fun n =>
        (- Real.log (fkZ (Gn n) (fsc_logistic t) q) + C) / n))
    (κ : ℝ) (hκ : κ ≠ 0)
    (he : Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 κ)) :
    ∃ (c : ℕ → ℝ) (κ' : ℝ),
      Subadditive (fun n => - Real.log (fkZ (Gn n) (fsc_logistic t) q) + c n)
      ∧ BddBelow (Set.range fun n =>
          (- Real.log (fkZ (Gn n) (fsc_logistic t) q) + c n) / n)
      ∧ Tendsto (fun n => c n / n) atTop (𝓝 0)
      ∧ κ' ≠ 0
      ∧ Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 κ') := by
  refine ⟨fun _ => C, κ, fis_subadditive_of_bounded hC hglue, hbdd, ?_, hκ, he⟩
  
  simpa using (tendsto_const_nhds (x := C)).div_atTop tendsto_natCast_atTop_atTop


end FK
end StatMech
