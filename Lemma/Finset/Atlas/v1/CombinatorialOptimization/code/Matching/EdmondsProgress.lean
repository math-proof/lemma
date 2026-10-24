import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Matching.EdmondsProgress
open SimpleGraph


namespace SimpleGraph

/--
[walk_level_induction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsProgress.lean)
-/
@[path]
lemma walk_level_induction
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : G.Subgraph}
  {F : AlternatingForest G M}
  {s t : V}
  {p : G.Walk s t}
-- given
  (hsat : ∀ u v, G.Adj u v → F.isEvenLevel u → v ∈ F.forestVerts ∧ Odd (F.level v))
  (halt : Walk.IsAlternatingFrom p M)
  (hs_forest : s ∈ F.forestVerts)
  (hs_even : Even (F.level s)) :
-- imply
  ∀ i, i ≤ p.length → p.getVert i ∈ F.forestVerts ∧ (Even i → Even (F.level (p.getVert i))) ∧ (Odd i → Odd (F.level (p.getVert i))) := by
-- proof
  intro i hi
  induction i with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rwa [Walk.getVert_zero]
    · intro _; rwa [Walk.getVert_zero]
    · intro h; exact absurd h (by decide)
  | succ k ih =>
    have hk_le : k ≤ p.length := Nat.le_of_succ_le hi
    have hk_lt : k < p.length := Nat.lt_of_succ_le hi
    obtain ⟨hk_mem, hk_even_imp, hk_odd_imp⟩ := ih hk_le
    have hadj_k : G.Adj (p.getVert k) (p.getVert (k + 1)) :=
      Walk.adj_getVert_succ p hk_lt
    have hk_edge_len : k < p.edges.length := by rw [Walk.length_edges]; exact hk_lt
    have hedge := halt k hk_edge_len
    have hedge_eq := Walk.edges_getElem_eq p k hk_edge_len
    by_cases hk_parity : Even k
    ·
      have hk_even_level := hk_even_imp hk_parity
      have hk_isEven : F.isEvenLevel (p.getVert k) := ⟨hk_mem, hk_even_level⟩
      have hsat_app := hsat (p.getVert k) (p.getVert (k + 1)) hadj_k hk_isEven
      refine ⟨hsat_app.1, ?_, ?_⟩
      · intro h_succ_even
        exact absurd (hk_parity.add_one) (Nat.not_odd_iff_even.mpr h_succ_even)
      · intro _; exact hsat_app.2
    ·
      have hk_odd : Odd k := Nat.not_even_iff_odd.mp hk_parity
      have hk_odd_level := hk_odd_imp hk_odd
      have hedge_M := hedge.2 hk_odd
      rw [hedge_eq] at hedge_M
      have hM_adj : M.Adj (p.getVert k) (p.getVert (k + 1)) :=
        Subgraph.mem_edgeSet.mp hedge_M
      have hpartner := F.matched_partner_even (p.getVert k) hk_mem hk_odd_level
        (p.getVert (k + 1)) hM_adj
      refine ⟨hpartner.1, ?_, ?_⟩
      · intro _; exact hpartner.2.1
      · intro h_succ_odd
        exact absurd h_succ_odd (Nat.not_odd_iff_even.mpr (hk_odd.add_one))

end SimpleGraph

namespace SimpleGraph

/--
[no_augmenting_path_of_saturated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsProgress.lean)
-/
@[path]
lemma no_augmenting_path_of_saturated
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : G.Subgraph}
  {F : AlternatingForest G M}
-- given
  (hsat : ∀ u v, G.Adj u v → F.isEvenLevel u → v ∈ F.forestVerts ∧ Odd (F.level v)) :
-- imply
  ¬ HasAugmentingPath G M := by
-- proof
  intro ⟨s, t, p, hpath, hst, hs_unmatched, ht_unmatched, halt⟩
  have hs_forest : s ∈ F.forestVerts := F.unmatched_are_roots s hs_unmatched
  have hs_level_zero : F.level s = 0 := F.unmatched_level_zero s hs_forest hs_unmatched
  have hs_even : Even (F.level s) := hs_level_zero ▸ ⟨0, by omega⟩
  have ht_forest : t ∈ F.forestVerts := F.unmatched_are_roots t ht_unmatched
  have hlen_pos : 0 < p.length := by
    cases p with
    | nil => exact absurd rfl hst
    | cons _ _ => exact Nat.succ_pos _
  have ht_info := walk_level_induction M F hsat p halt hs_forest hs_even p.length (le_refl _)
  rw [Walk.getVert_length] at ht_info
  obtain ⟨_, ht_even_imp, ht_odd_imp⟩ := ht_info
  by_cases h_len_even : Even p.length
  ·
    have hlast_pos : p.length - 1 < p.length := Nat.sub_lt hlen_pos Nat.one_pos
    have hlast_edge_len : p.length - 1 < p.edges.length := by
      rw [Walk.length_edges]; exact hlast_pos
    have hlast_odd : Odd (p.length - 1) := by
      obtain ⟨k, hk⟩ := h_len_even
      exact ⟨k - 1, by omega⟩
    have hedge_last := (halt (p.length - 1) hlast_edge_len).2 hlast_odd
    have hedge_eq_last := Walk.edges_getElem_eq p (p.length - 1) hlast_edge_len
    rw [hedge_eq_last] at hedge_last
    have hlen_sub : p.length - 1 + 1 = p.length := Nat.succ_pred_eq_of_pos hlen_pos
    rw [hlen_sub, Walk.getVert_length] at hedge_last
    have hM_adj_t : M.Adj (p.getVert (p.length - 1)) t := Subgraph.mem_edgeSet.mp hedge_last
    exact ht_unmatched (M.edge_vert hM_adj_t.symm)
  ·
    have h_len_odd : Odd p.length := Nat.not_even_iff_odd.mp h_len_even
    exact ht_unmatched (F.odd_level_matched t ht_forest (ht_odd_imp h_len_odd))

end SimpleGraph

namespace SimpleGraph

/--
[edmonds_progress](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsProgress.lean)
-/
@[path]
lemma edmonds_progress
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : G.Subgraph}
  {F : AlternatingForest G M}
-- given
  (hM : M.IsMatching) :
-- imply
  (∃ u v, G.Adj u v ∧ F.isEvenLevel u ∧ v ∉ F.forestVerts) ∨ (∃ u v, G.Adj u v ∧ F.isEvenLevel u ∧ F.isEvenLevel v ∧ F.root u = F.root v) ∨ (∃ u v, G.Adj u v ∧ F.isEvenLevel u ∧ F.isEvenLevel v ∧ F.root u ≠ F.root v) ∨ Subgraph.IsMaxMatching M := by
-- proof
  by_cases h : ∀ u v, G.Adj u v → F.isEvenLevel u → v ∈ F.forestVerts ∧ Odd (F.level v)
  ·
    right; right; right
    exact (berge_lemma M hM (Set.toFinite _)).mpr (no_augmenting_path_of_saturated M F h)
  ·
    push_neg at h
    obtain ⟨u, v, hadj, heven_u, hv⟩ := h
    by_cases hv_mem : v ∈ F.forestVerts
    ·
      have hv_not_odd : ¬ Odd (F.level v) := hv hv_mem
      have hv_even : Even (F.level v) := Nat.not_odd_iff_even.mp hv_not_odd
      have hv_even_level : F.isEvenLevel v := ⟨hv_mem, hv_even⟩
      by_cases hroot : F.root u = F.root v
      ·
        right; left
        exact ⟨u, v, hadj, heven_u, hv_even_level, hroot⟩
      ·
        right; right; left
        exact ⟨u, v, hadj, heven_u, hv_even_level, hroot⟩
    ·
      left
      exact ⟨u, v, hadj, heven_u, hv_mem⟩

end SimpleGraph


-- created on 2026-10-23
