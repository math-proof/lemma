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
import Def.StatisticalMechanics.Code.FK.SuperMultiplicative.Part3
open scoped BigOperators
open SimpleGraph Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

section Iso

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]


theorem fsm_numClusters_iso (φ : G ≃g H) (ω : Sym2 W → Bool) :
    numClusters G (fun e => ω (Sym2.map φ.toEquiv e)) = numClusters H ω := by
  unfold numClusters
  exact Fintype.card_congr (SimpleGraph.Iso.connectedComponentEquiv (fsm_openSubIso G H φ ω))


theorem fsm_edgeProduct_iso (φ : G ≃g H) (p : ℝ) (ω : Sym2 W → Bool) :
    edgeProduct G p (fun e => ω (Sym2.map φ.toEquiv e)) = edgeProduct H p ω := by
  classical
  unfold edgeProduct
  
  have himg : G.edgeFinset.image (Sym2.map φ.toEquiv) = H.edgeFinset := by
    ext e
    simp only [Finset.mem_image, mem_edgeFinset]
    constructor
    · rintro ⟨z, hz, rfl⟩
      induction z using Sym2.ind with
      | _ a b =>
        rw [mem_edgeSet] at hz
        rw [Sym2.map_mk, mem_edgeSet]; exact φ.map_rel_iff.mpr hz
    · intro he
      refine ⟨Sym2.map φ.toEquiv.symm e, ?_, ?_⟩
      · induction e using Sym2.ind with
        | _ a b =>
          rw [mem_edgeSet] at he
          rw [Sym2.map_mk, mem_edgeSet]
          have := φ.symm.map_rel_iff.mpr (show H.Adj a b from he)
          simpa using this
      · induction e using Sym2.ind with
        | _ a b =>
          simp only [Sym2.map_mk, Sym2.eq_iff]
          exact Or.inl ⟨RelIso.apply_symm_apply φ a, RelIso.apply_symm_apply φ b⟩
  calc ∏ e ∈ G.edgeFinset, (if ω (Sym2.map φ.toEquiv e) then p else 1 - p)
      = ∏ e ∈ G.edgeFinset.image (Sym2.map φ.toEquiv), (if ω e then p else 1 - p) := by
        rw [Finset.prod_image
          (fun x _ y _ h => Sym2.map.injective φ.toEquiv.injective h)]
    _ = ∏ e ∈ H.edgeFinset, (if ω e then p else 1 - p) := by rw [himg]


theorem fsm_fkZ_iso (φ : G ≃g H) (p q : ℝ) :
    fkZ G p q = fkZ H p q := by
  classical
  unfold fkZ
  
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (fsm_sym2Congr φ.toEquiv) (Equiv.refl Bool))
    (fun ω => fkWeight G p q ω) (fun ω => fkWeight H p q ω) ?_
  intro ωV
  
  have hpb : (Equiv.arrowCongr (fsm_sym2Congr φ.toEquiv) (Equiv.refl Bool)) ωV
      = fun w => ωV (Sym2.map φ.symm.toEquiv w) := by
    funext w
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, id_eq, Function.comp,
      fsm_sym2Congr, Equiv.coe_fn_symm_mk]
    rfl
  rw [hpb]
  show fkWeight G p q ωV = fkWeight H p q (fun w => ωV (Sym2.map φ.symm.toEquiv w))
  unfold fkWeight
  rw [fsm_edgeProduct_iso H G φ.symm p ωV, fsm_numClusters_iso H G φ.symm ωV]

end Iso


section Fekete

variable {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
  (Gn : ∀ n, SimpleGraph (V n)) [∀ n, DecidableRel (Gn n).Adj]


theorem fsm_subadditive_neglog_fkZ {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hjux : ∀ m n, Gn (m + n) ≃g Gn m ⊕g Gn n) :
    Subadditive (fun n => - Real.log (fkZ (Gn n) p q)) := by
  intro m n
  simp only
  rw [fsm_fkZ_iso (Gn (m + n)) (Gn m ⊕g Gn n) (hjux m n) p q]
  exact fsm_neglog_sum_le (Gn m) (Gn n) hp hp1 hq


theorem fsm_fekete_limit (q : ℝ) (hq : 0 < q)
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (hjux : ∀ m n, Gn (m + n) ≃g Gn m ⊕g Gn n)
    (hbdd : ∀ t, BddBelow (Set.range fun n =>
      (- Real.log (fkZ (Gn n) (fsc_logistic t) q)) / n))
    (c : ℝ → ℝ) (hc : ∀ t, c t ≠ 0)
    (he : ∀ t, Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 (c t))) :
    ∃ g : ℝ → ℝ,
      (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) q t) atTop (𝓝 (g t)))
        ∧ ConvexOn ℝ Set.univ g := by
  have hsuper : ∀ t, Subadditive (fun n => - Real.log (fkZ (Gn n) (fsc_logistic t) q)) :=
    fun t => fsm_subadditive_neglog_fkZ Gn (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
      hjux
  exact fkl_fekete_limit Gn q hq hE hsuper hbdd c hc he

end Fekete


theorem fsm_juxtaposition_satisfiable (m n : ℕ) :
    Nonempty ((⊥ : SimpleGraph (Fin (m + n))) ≃g
      (⊥ : SimpleGraph (Fin m)) ⊕g (⊥ : SimpleGraph (Fin n))) := by
  refine ⟨⟨finSumFinEquiv.symm, ?_⟩⟩
  intro a b
  
  simp only [SimpleGraph.bot_adj]
  constructor
  · intro h
    
    match finSumFinEquiv.symm a, finSumFinEquiv.symm b, h with
    | Sum.inl _, Sum.inl _, h => simp only [SimpleGraph.sum_adj, SimpleGraph.bot_adj] at h
    | Sum.inr _, Sum.inr _, h => simp only [SimpleGraph.sum_adj, SimpleGraph.bot_adj] at h
    | Sum.inl _, Sum.inr _, h => simp only [SimpleGraph.sum_adj] at h
    | Sum.inr _, Sum.inl _, h => simp only [SimpleGraph.sum_adj] at h
  · intro h; exact h.elim

end FK
end StatMech
