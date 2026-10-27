import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.CombinatorialOptimization.code.Matching.Berge
open SimpleGraph SimpleGraph.Walk


namespace SimpleGraph.Walk

/--
[edges_getElem_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Berge.lean)
-/
@[path]
lemma edges_getElem_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
  {i : ℕ}
-- given
  (hi : i < p.edges.length) :
-- imply
  p.edges[i] = s(p.getVert i, p.getVert (i + 1)) := by
-- proof
  induction p generalizing i with
  | nil => simp at hi
  | cons h q ih =>
    cases i with
    | zero => simp [Walk.edges_cons, Walk.getVert]
    | succ j => simp only [Walk.edges_cons, List.getElem_cons_succ, Walk.getVert]; apply ih

end SimpleGraph.Walk

namespace SimpleGraph

/--
[augmenting_path_odd_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Berge.lean)
-/
@[path]
lemma augmenting_path_odd_length
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {M : G.Subgraph}
  {p : G.Walk u v}
-- given
  (haug : p.IsAugmentingPath M) :
-- imply
  Odd p.edges.length := by
-- proof
  obtain ⟨_, hne, _, hv_not_M, halt⟩ := haug
  have hlen : 0 < p.edges.length := by
    cases p with | nil => exact absurd rfl hne | cons _ _ => simp [Walk.edges_cons]
  by_contra h_not_odd
  rw [Nat.not_odd_iff_even] at h_not_odd
  have h_last_odd : Odd (p.edges.length - 1) := by
    obtain ⟨k, hk⟩ := h_not_odd; exact ⟨k - 1, by omega⟩
  have h_last_idx : p.edges.length - 1 < p.edges.length := Nat.sub_lt hlen Nat.one_pos
  have h_last_in_M := (halt _ h_last_idx).2 h_last_odd
  rw [Walk.edges_getElem_eq p _ h_last_idx] at h_last_in_M
  have h_getvert_last : p.getVert (p.edges.length - 1 + 1) = v := by
    have : p.edges.length - 1 + 1 = p.edges.length := Nat.sub_add_cancel hlen
    rwa [this, show p.edges.length = p.length from p.length_edges]
  rw [h_getvert_last] at h_last_in_M
  exact hv_not_M (Subgraph.mem_edgeSet.mp h_last_in_M).snd_mem

end SimpleGraph

namespace SimpleGraph

/--
[edge_incident_of_path](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Berge.lean)
-/
@[path]
lemma edge_incident_of_path
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
  {n : ℕ}
  {z : V}
-- given
  (hpath : p.IsPath)
  (hn_pos : 0 < n)
  (hn_lt : n < p.length)
  (hz : s(p.getVert n, z) ∈ p.edges) :
-- imply
  z = p.getVert (n - 1) ∨ z = p.getVert (n + 1) := by
-- proof
  rw [List.mem_iff_getElem] at hz
  obtain ⟨j, hj_lt, hj_eq⟩ := hz
  rw [Walk.edges_getElem_eq p j hj_lt] at hj_eq
  have hlen_eq := p.length_edges
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp hj_eq
  · have hj_n : j = n := hpath.getVert_injOn (by simp; omega) (by simp; omega) h1
    subst hj_n; exact Or.inr h2.symm
  · have hj1_n : j + 1 = n := hpath.getVert_injOn (by simp; omega) (by simp; omega) h2
    have : j = n - 1 := by omega
    subst this; exact Or.inl h1.symm

end SimpleGraph

namespace SimpleGraph

/--
[symmDiffMatching_isMatching](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Berge.lean)
-/
@[path]
lemma symmDiffMatching_isMatching
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {M : G.Subgraph}
  {p : G.Walk u v}
-- given
  (hM : M.IsMatching)
  (haug : p.IsAugmentingPath M) :
-- imply
  (symmDiffMatching M p).IsMatching := by
-- proof
  classical
  have hpath := haug.1
  have hne := haug.2.1
  have hu_notM := haug.2.2.1
  have hv_notM := haug.2.2.2.1
  have halt := haug.2.2.2.2
  have hlen : 0 < p.edges.length := by
    cases p with | nil => exact absurd rfl hne | cons _ _ => simp [Walk.edges_cons]
  have hlen_eq : p.edges.length = p.length := p.length_edges
  have hodd : Odd p.edges.length := augmenting_path_odd_length haug
  intro w hw
  simp only [symmDiffMatching, Set.mem_union, Set.mem_setOf_eq] at hw
  by_cases hwP : w ∈ p.support
  ·
    rw [Walk.mem_support_iff_exists_getVert] at hwP
    obtain ⟨n, hn_eq, hn_le⟩ := hwP
    subst hn_eq
    by_cases hn0 : n = 0
    ·
      subst hn0; simp only [Walk.getVert_zero]
      have hedge0 : p.edges[0] = s(u, p.getVert 1) := by
        have h := Walk.edges_getElem_eq p 0 hlen; rwa [Walk.getVert_zero] at h
      have h0_notM : s(u, p.getVert 1) ∉ M.edgeSet := by
        rw [← hedge0]; exact (halt 0 hlen).1 ⟨0, by ring⟩
      have h0_mem : s(u, p.getVert 1) ∈ p.edges.toFinset := by
        rw [List.mem_toFinset, ← hedge0]; exact List.getElem_mem hlen
      refine ⟨p.getVert 1, Or.inr ⟨Walk.adj_of_mem_edges p (List.mem_toFinset.mp h0_mem),
        h0_mem, fun h => h0_notM (Subgraph.mem_edgeSet.mpr h)⟩, ?_⟩
      intro z hz
      obtain ⟨hz_M, _⟩ | ⟨_, hz_mem, _⟩ := hz
      · exact absurd (M.edge_vert hz_M) hu_notM
      · have hz_edges := List.mem_toFinset.mp hz_mem
        rw [List.mem_iff_getElem] at hz_edges
        obtain ⟨j, hj_lt, hj_eq⟩ := hz_edges
        rw [Walk.edges_getElem_eq p j hj_lt] at hj_eq
        obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp hj_eq
        · exact ((hpath.getVert_eq_start_iff (by omega)).mp h1 ▸ h2).symm
        · exact absurd ((hpath.getVert_eq_start_iff (by omega)).mp h2) (by omega)
    · by_cases hnl : n = p.length
      ·
        subst hnl; rw [Walk.getVert_length]
        set L := p.edges.length - 1
        have hL_lt : L < p.edges.length := Nat.sub_lt hlen Nat.one_pos
        have hedgeL : p.edges[L] = s(p.getVert L, v) := by
          have h := Walk.edges_getElem_eq p L hL_lt
          rwa [show L + 1 = p.edges.length from Nat.sub_add_cancel hlen,
            hlen_eq, Walk.getVert_length] at h
        have hL_even : Even L := by obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩
        have hL_notM : s(p.getVert L, v) ∉ M.edgeSet := by
          rw [← hedgeL]; exact (halt L hL_lt).1 hL_even
        have hL_mem : s(p.getVert L, v) ∈ p.edges.toFinset := by
          rw [List.mem_toFinset, ← hedgeL]; exact List.getElem_mem hL_lt
        refine ⟨p.getVert L, Or.inr ⟨(Walk.adj_of_mem_edges p (List.mem_toFinset.mp hL_mem)).symm,
          by rw [Sym2.eq_swap]; exact hL_mem,
          fun h => hL_notM (by rw [Sym2.eq_swap]; exact Subgraph.mem_edgeSet.mpr h)⟩, ?_⟩
        intro z hz
        obtain ⟨hz_M, _⟩ | ⟨_, hz_mem, _⟩ := hz
        · exact absurd (M.edge_vert hz_M) hv_notM
        · have hz_edges := List.mem_toFinset.mp hz_mem
          rw [List.mem_iff_getElem] at hz_edges
          obtain ⟨j, hj_lt, hj_eq⟩ := hz_edges
          rw [Walk.edges_getElem_eq p j hj_lt] at hj_eq
          obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp hj_eq
          · exact absurd ((hpath.getVert_eq_end_iff (by omega)).mp h1) (by omega)
          · have : j + 1 = p.length := (hpath.getVert_eq_end_iff (by omega)).mp h2
            have : j = L := by omega
            subst this; exact h1.symm
      ·
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_lt : n < p.length := lt_of_le_of_ne hn_le hnl
        have hn_lt_edges : n < p.edges.length := by omega
        have hn1_lt_edges : n - 1 < p.edges.length := by omega
        have hedge_n : p.edges[n] = s(p.getVert n, p.getVert (n + 1)) :=
          Walk.edges_getElem_eq p n hn_lt_edges
        have hedge_n1 : p.edges[n - 1] = s(p.getVert (n - 1), p.getVert n) := by
          have h := Walk.edges_getElem_eq p (n - 1) hn1_lt_edges
          rwa [show n - 1 + 1 = n from Nat.sub_add_cancel hn_pos] at h
        have h_n_mem : s(p.getVert n, p.getVert (n + 1)) ∈ p.edges.toFinset := by
          rw [List.mem_toFinset, ← hedge_n]; exact List.getElem_mem hn_lt_edges
        have h_n1_mem : s(p.getVert (n - 1), p.getVert n) ∈ p.edges.toFinset := by
          rw [List.mem_toFinset, ← hedge_n1]; exact List.getElem_mem hn1_lt_edges
        obtain hn_even | hn_odd := Nat.even_or_odd n
        ·
          have hn1_odd : Odd (n - 1) := by
            obtain ⟨k, hk⟩ := hn_even; exact ⟨k - 1, by omega⟩
          have h_n_notM : s(p.getVert n, p.getVert (n + 1)) ∉ M.edgeSet := by
            rw [← hedge_n]; exact (halt n hn_lt_edges).1 hn_even
          have h_n1_inM : s(p.getVert (n - 1), p.getVert n) ∈ M.edgeSet := by
            rw [← hedge_n1]; exact (halt (n - 1) hn1_lt_edges).2 hn1_odd
          have hM_prev : M.Adj (p.getVert n) (p.getVert (n - 1)) :=
            (Subgraph.mem_edgeSet.mp h_n1_inM).symm
          have hw_M : p.getVert n ∈ M.verts := M.edge_vert hM_prev
          refine ⟨p.getVert (n + 1), Or.inr
            ⟨Walk.adj_of_mem_edges p (List.mem_toFinset.mp h_n_mem),
              h_n_mem, fun h => h_n_notM (Subgraph.mem_edgeSet.mpr h)⟩, ?_⟩
          intro z hz
          obtain ⟨hz_M, hz_notP⟩ | ⟨_, hz_mem, hz_notM⟩ := hz
          · obtain ⟨_, _, huniq⟩ := hM hw_M
            have hz_eq : z = p.getVert (n - 1) :=
              (huniq z hz_M).trans (huniq _ hM_prev).symm
            rw [hz_eq] at hz_notP
            exact absurd (by rw [Sym2.eq_swap]; exact h_n1_mem) hz_notP
          · rcases edge_incident_of_path hpath hn_pos hn_lt z
            (List.mem_toFinset.mp hz_mem) with h | h
            · rw [h] at hz_notM; exact absurd hM_prev hz_notM
            · exact h
        ·
          have hn1_even : Even (n - 1) := by
            obtain ⟨k, hk⟩ := hn_odd; exact ⟨k, by omega⟩
          have h_n_inM : s(p.getVert n, p.getVert (n + 1)) ∈ M.edgeSet := by
            rw [← hedge_n]; exact (halt n hn_lt_edges).2 hn_odd
          have h_n1_notM : s(p.getVert (n - 1), p.getVert n) ∉ M.edgeSet := by
            rw [← hedge_n1]; exact (halt (n - 1) hn1_lt_edges).1 hn1_even
          have hM_next : M.Adj (p.getVert n) (p.getVert (n + 1)) :=
            Subgraph.mem_edgeSet.mp h_n_inM
          have hw_M : p.getVert n ∈ M.verts := M.edge_vert hM_next
          have hGadj_n1 : G.Adj (p.getVert n) (p.getVert (n - 1)) :=
            (Walk.adj_of_mem_edges p (List.mem_toFinset.mp h_n1_mem)).symm
          have hnotM_n1 : ¬ M.Adj (p.getVert n) (p.getVert (n - 1)) := by
            intro h
            exact h_n1_notM (by rw [Sym2.eq_swap]; exact Subgraph.mem_edgeSet.mpr h)
          refine ⟨p.getVert (n - 1), Or.inr
            ⟨hGadj_n1, by rw [Sym2.eq_swap]; exact h_n1_mem, hnotM_n1⟩, ?_⟩
          intro z hz
          obtain ⟨hz_M, hz_notP⟩ | ⟨_, hz_mem, hz_notM⟩ := hz
          · obtain ⟨_, _, huniq⟩ := hM hw_M
            have hz_eq : z = p.getVert (n + 1) :=
              (huniq z hz_M).trans (huniq _ hM_next).symm
            rw [hz_eq] at hz_notP; exact absurd h_n_mem hz_notP
          · rcases edge_incident_of_path hpath hn_pos hn_lt z
            (List.mem_toFinset.mp hz_mem) with h | h
            · exact h
            · rw [h] at hz_notM; exact absurd hM_next hz_notM
  ·
    have hw_M : w ∈ M.verts := hw.elim id (fun h => absurd h hwP)
    obtain ⟨y, hy_adj, hy_uniq⟩ := hM hw_M
    refine ⟨y, Or.inl ⟨hy_adj, fun hmem =>
      hwP (Walk.fst_mem_support_of_mem_edges p (List.mem_toFinset.mp hmem))⟩, ?_⟩
    intro z hz
    obtain ⟨hz_M, _⟩ | ⟨_, hz_mem, _⟩ := hz
    · exact hy_uniq z hz_M
    · exact absurd (Walk.fst_mem_support_of_mem_edges p (List.mem_toFinset.mp hz_mem)) hwP

end SimpleGraph

namespace SimpleGraph

/--
[symmDiffMatching_edgeSet_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Berge.lean)
-/
@[path]
lemma symmDiffMatching_edgeSet_ncard
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {M : G.Subgraph}
  {p : G.Walk u v}
-- given
  (hM : M.IsMatching)
  (haug : p.IsAugmentingPath M)
  (hfin : M.edgeSet.Finite) :
-- imply
  M.edgeSet.ncard < (symmDiffMatching M p).edgeSet.ncard := by
-- proof
  classical
  set P := p.edges.toFinset
  have hM'_eq : (symmDiffMatching M p).edgeSet = (M.edgeSet \ ↑P) ∪ (↑P \ M.edgeSet) := by
    ext e
    simp only [Subgraph.mem_edgeSet, symmDiffMatching, Set.mem_union, Set.mem_diff,
      Finset.mem_coe]
    constructor
    · intro h; induction e using Sym2.ind with
      | h a b =>
        obtain ⟨hM_ab, hnP⟩ | ⟨hG, hP_ab, hnM⟩ := h
        · left; exact ⟨Subgraph.mem_edgeSet.mpr hM_ab, hnP⟩
        · right; exact ⟨hP_ab, fun hm => hnM (Subgraph.mem_edgeSet.mp hm)⟩
    · intro h; induction e using Sym2.ind with
      | h a b =>
        obtain ⟨hM_ab, hnP⟩ | ⟨hP_ab, hnM⟩ := h
        · left; exact ⟨Subgraph.mem_edgeSet.mp hM_ab, hnP⟩
        · right; exact ⟨Walk.adj_of_mem_edges p (List.mem_toFinset.mp hP_ab), hP_ab,
          fun h => hnM (Subgraph.mem_edgeSet.mpr h)⟩
  have hM'_card : (symmDiffMatching M p).edgeSet.ncard =
    (M.edgeSet \ ↑P).ncard + (↑P \ M.edgeSet).ncard := by
    rw [hM'_eq]
    exact Set.ncard_union_eq disjoint_sdiff_sdiff hfin.diff P.finite_toSet.diff
  have hM_decomp : M.edgeSet.ncard = (M.edgeSet \ ↑P).ncard + (M.edgeSet ∩ ↑P).ncard := by
    have h1 : Disjoint (M.edgeSet \ ↑P) (M.edgeSet ∩ ↑P) :=
      Set.disjoint_of_subset_right Set.inter_subset_right Set.disjoint_sdiff_left
    calc M.edgeSet.ncard
      = (M.edgeSet \ ↑P ∪ M.edgeSet ∩ ↑P).ncard := by rw [Set.diff_union_inter]
      _ = _ := Set.ncard_union_eq h1 hfin.diff (hfin.inter_of_left _)
  have hPdiffM : (↑P \ M.edgeSet).ncard = (P.filter (fun e => e ∉ M.edgeSet)).card := by
    have h : (↑P \ M.edgeSet : Set (Sym2 V)) = ↑(P.filter (fun e => e ∉ M.edgeSet)) := by
      ext x; simp [Set.mem_diff]
    rw [h, Set.ncard_coe_finset]
  have hMinterP : (M.edgeSet ∩ ↑P).ncard = (P.filter (fun e => e ∈ M.edgeSet)).card := by
    have h : (M.edgeSet ∩ ↑P : Set (Sym2 V)) = ↑(P.filter (fun e => e ∈ M.edgeSet)) := by
      ext x; simp [Set.mem_inter_iff, and_comm]
    rw [h, Set.ncard_coe_finset]
  have hnd : p.edges.Nodup := haug.1.isTrail.edges_nodup
  obtain ⟨k, hk⟩ := augmenting_path_odd_length haug
  have halt := haug.2.2.2.2
  have h_nonM_ge : k + 1 ≤ (P.filter (fun e => e ∉ M.edgeSet)).card := by
    have h_inj : Function.Injective (fun (i : Fin (k + 1)) =>
      p.edges[2 * i.val]'(by have := i.isLt; omega)) := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ hij; simp only at hij
      exact Fin.ext (by
        simp only [Fin.mk.injEq]
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
          ((List.Nodup.getElem_inj_iff hnd).mp hij))
    have h_sub : Finset.univ.image (fun (i : Fin (k + 1)) =>
      p.edges[2 * i.val]'(by have := i.isLt; omega)) ⊆
      P.filter (fun e => e ∉ M.edgeSet) := by
      intro e he
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at he
      obtain ⟨⟨i, hi⟩, rfl⟩ := he
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.getElem_mem (by omega)),
        (halt (2 * i) (by omega)).1 ⟨i, by ring⟩⟩
    have h1 := Finset.card_le_card h_sub
    have h2 := Finset.card_image_of_injective Finset.univ h_inj
    simp at h2; linarith
  have h_M_ge : k ≤ (P.filter (fun e => e ∈ M.edgeSet)).card := by
    have h_inj : Function.Injective (fun (i : Fin k) =>
      p.edges[2 * i.val + 1]'(by have := i.isLt; omega)) := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ hij; simp only at hij
      exact Fin.ext (by
        simp only [Fin.mk.injEq]
        have heq := (List.Nodup.getElem_inj_iff hnd).mp hij; omega)
    have h_sub : Finset.univ.image (fun (i : Fin k) =>
      p.edges[2 * i.val + 1]'(by have := i.isLt; omega)) ⊆
      P.filter (fun e => e ∈ M.edgeSet) := by
      intro e he
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at he
      obtain ⟨⟨i, hi⟩, rfl⟩ := he
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.getElem_mem (by omega)),
        (halt (2 * i + 1) (by omega)).2 ⟨i, by ring⟩⟩
    have h1 := Finset.card_le_card h_sub
    have h2 := Finset.card_image_of_injective Finset.univ h_inj
    simp at h2; linarith
  have h_total : (P.filter (fun e => e ∈ M.edgeSet)).card +
    (P.filter (fun e => e ∉ M.edgeSet)).card = 2 * k + 1 := by
    have hpc : P.card = 2 * k + 1 := by
      simp only [P]; rw [List.toFinset_card_of_nodup hnd, hk]
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := P) (p := fun e => e ∈ M.edgeSet)
    have heq : P.filter (fun a => ¬ a ∈ M.edgeSet) = P.filter (fun e => e ∉ M.edgeSet) := by
      ext; simp
    linarith [heq ▸ h]
  linarith [hM'_card, hM_decomp, hPdiffM, hMinterP, h_nonM_ge, h_M_ge, h_total]

end SimpleGraph

namespace SimpleGraph

/--
[augmenting_path_gives_larger_matching](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Berge.lean)
-/
@[path]
lemma augmenting_path_gives_larger_matching
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableEq V]
  {G : SimpleGraph V}
  {M : G.Subgraph}
  {u v : V}
  {p : G.Walk u v}
-- given
  (hM : M.IsMatching)
  (haug : p.IsAugmentingPath M) :
-- imply
  ∃ M' : G.Subgraph, M'.IsMatching ∧ M.edgeSet.ncard < M'.edgeSet.ncard := by
-- proof
  classical
  by_cases hfin : M.edgeSet.Finite
  · exact ⟨symmDiffMatching M p, symmDiffMatching_isMatching M hM p haug,
    symmDiffMatching_edgeSet_ncard M hM p haug hfin⟩
  ·
    have hne : u ≠ v := haug.2.1
    obtain ⟨w, hadj_uw, q, rfl⟩ :
      ∃ w, ∃ h : G.Adj u w, ∃ q : G.Walk w v, p = Walk.cons h q := by
      cases p with
      | nil => exact absurd rfl hne
      | cons h q => exact ⟨_, h, q, rfl⟩
    refine ⟨G.subgraphOfAdj hadj_uw, Subgraph.IsMatching.subgraphOfAdj hadj_uw, ?_⟩
    have hinf : M.edgeSet.Infinite := Set.not_finite.mp hfin
    simp [hinf.ncard, edgeSet_subgraphOfAdj, Set.ncard_singleton]

end SimpleGraph

namespace SimpleGraph

/--
[matching_verts_twice_edges](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Berge.lean)
-/
@[path]
lemma matching_verts_twice_edges
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableEq V]
  {G : SimpleGraph V}
  {M : G.Subgraph}
-- given
  (hM : M.IsMatching)
  (hfin : M.edgeSet.Finite) :
-- imply
  M.verts.ncard = 2 * M.edgeSet.ncard := by
-- proof
  classical
  haveI : Fintype ↑M.edgeSet := hfin.fintype
  have hvfin : M.verts.Finite := by
    rw [← hM.support_eq_verts]
    apply Set.Finite.subset (hfin.biUnion (fun e _ => (Sym2.toFinset e).finite_toSet))
    intro v hv
    rw [Subgraph.mem_support] at hv
    obtain ⟨w, hw⟩ := hv
    exact Set.mem_biUnion (Subgraph.mem_edgeSet.mpr hw)
      (show v ∈ (↑(Sym2.toFinset s(v, w)) : Set V) by simp [Sym2.mem_toFinset])
  haveI : Fintype ↑M.verts := hvfin.fintype
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
    Set.ncard_eq_toFinset_card', Set.toFinset_card]
  suffices hfib : ∀ e : ↑M.edgeSet, Fintype.card {v : ↑M.verts // hM.toEdge v = e} = 2 by
    calc Fintype.card ↑M.verts
      = Fintype.card (Σ (e : ↑M.edgeSet), {v : ↑M.verts // hM.toEdge v = e}) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv hM.toEdge).symm
      _ = ∑ e : ↑M.edgeSet, Fintype.card {v : ↑M.verts // hM.toEdge v = e} :=
        Fintype.card_sigma
      _ = ∑ _ : ↑M.edgeSet, 2 := by congr 1; ext e; exact hfib e
      _ = 2 * Fintype.card ↑M.edgeSet := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
  intro ⟨e, he⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.exists.mp ⟨e, rfl⟩
  have hadj : M.Adj a b := Subgraph.mem_edgeSet.mp he
  have ha : a ∈ M.verts := hadj.fst_mem
  have hb : b ∈ M.verts := hadj.snd_mem
  have hab : a ≠ b := (M.adj_sub hadj).ne
  have hfib_a : hM.toEdge ⟨a, ha⟩ = ⟨s(a, b), he⟩ :=
    hM.toEdge_eq_of_adj ha hadj
  have hfib_b : hM.toEdge ⟨b, hb⟩ = ⟨s(a, b), he⟩ := by
    have h := hM.toEdge_eq_of_adj hb (M.symm hadj)
    rw [Subtype.ext_iff] at h ⊢
    simp only at h ⊢
    rw [h, Sym2.eq_swap]
  have hne : (⟨a, ha⟩ : M.verts) ≠ ⟨b, hb⟩ := by
    simp [Subtype.mk.injEq, hab]
  have hcard' : Fintype.card {v : ↑M.verts // v = ⟨a, ha⟩ ∨ v = ⟨b, hb⟩} = 2 :=
    Fintype.card_subtype_eq_or_eq_of_ne hne
  rw [← hcard']
  apply Fintype.card_congr
  refine {
    toFun := fun ⟨v, hv⟩ => ⟨v, ?_⟩
    invFun := fun ⟨v, hv⟩ => ⟨v, ?_⟩
    left_inv := fun ⟨v, hv⟩ => by simp
    right_inv := fun ⟨v, hv⟩ => by simp
  }
  · have hval : (hM.toEdge v).val = s(a, b) := by rw [hv]
    have hv_mem : v.val ∈ (hM.toEdge v).val := by
      unfold Subgraph.IsMatching.toEdge; simp [Sym2.mem_iff]
    rw [hval] at hv_mem
    obtain h | h := Sym2.mem_iff.mp hv_mem
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  · rcases hv with rfl | rfl
    · exact hfib_a
    · exact hfib_b

end SimpleGraph

namespace SimpleGraph

/--
[matchingSwapEdge_isMatching](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Berge.lean)
-/
@[path]
lemma matchingSwapEdge_isMatching
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableEq V]
  {G : SimpleGraph V}
  {Mstar' : G.Subgraph}
  {u v w : V}
-- given
  (hMstar' : Mstar'.IsMatching)
  (hAdj : Mstar'.Adj u v)
  (hGvw : G.Adj v w)
  (hw_fresh : w ∉ Mstar'.verts) :
-- imply
  (matchingSwapEdge Mstar' u v w hMstar' hAdj hGvw hw_fresh).IsMatching := by
-- proof
  intro z hz
  simp only [matchingSwapEdge] at hz ⊢
  obtain ⟨hz_Mstar, hz_ne_u⟩ | rfl := hz
  · rw [Set.mem_singleton_iff] at hz_ne_u
    obtain ⟨y, hy, hy_uniq⟩ := hMstar' hz_Mstar
    by_cases hzv : z = v
    · subst hzv
      refine ⟨w, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
      intro b hb
      obtain ⟨hadj_b, hne1, hne2⟩ | ⟨_, rfl⟩ | ⟨rfl, _⟩ := hb
      · exact absurd ⟨rfl, (hy_uniq b hadj_b).trans (hy_uniq u (Mstar'.symm hAdj)).symm⟩ hne2
      · rfl
      · exact absurd hz_Mstar hw_fresh
    · have hzw : z ≠ w := fun h => hw_fresh (h ▸ hz_Mstar)
      refine ⟨y, Or.inl ⟨hy, fun ⟨rfl, rfl⟩ => hz_ne_u rfl, fun ⟨rfl, _⟩ => hzv rfl⟩, ?_⟩
      intro b hb
      obtain ⟨hadj_b, _, _⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hb
      · exact hy_uniq b hadj_b
      · exact absurd rfl hzv
      · exact absurd rfl hzw
  · refine ⟨v, Or.inr (Or.inr ⟨rfl, rfl⟩), ?_⟩
    intro b hb
    obtain ⟨hadj_b, _, _⟩ | ⟨rfl, _⟩ | ⟨_, rfl⟩ := hb
    · exact absurd (Mstar'.edge_vert hadj_b) hw_fresh
    · exact absurd (Mstar'.edge_vert (Mstar'.symm hAdj)) hw_fresh
    · rfl

end SimpleGraph

namespace SimpleGraph

/--
[matchingSwapEdge_edgeSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Berge.lean)
-/
@[path]
lemma matchingSwapEdge_edgeSet_finite
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableEq V]
  {G : SimpleGraph V}
  {Mstar' : G.Subgraph}
  {u v w : V}
-- given
  (hMstar' : Mstar'.IsMatching)
  (hAdj : Mstar'.Adj u v)
  (hGvw : G.Adj v w)
  (hw_fresh : w ∉ Mstar'.verts)
  (hfin : Mstar'.edgeSet.Finite) :
-- imply
  (matchingSwapEdge Mstar' u v w hMstar' hAdj hGvw hw_fresh).edgeSet.Finite := by
-- proof
  apply Set.Finite.subset (hfin.union (Set.finite_singleton s(v, w)))
  intro e he
  simp only [matchingSwapEdge, Subgraph.mem_edgeSet] at he
  induction e using Sym2.ind with
  | h a b =>
    obtain ⟨hadj, _, _⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := he
    · exact Or.inl (Subgraph.mem_edgeSet.mpr hadj)
    · exact Or.inr (Set.mem_singleton_iff.mpr rfl)
    · exact Or.inr (Set.mem_singleton_iff.mpr Sym2.eq_swap)

end SimpleGraph

namespace SimpleGraph

/--
[matchingSwapEdge_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Berge.lean)
-/
@[path]
lemma matchingSwapEdge_ncard
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableEq V]
  {G : SimpleGraph V}
  {Mstar' : G.Subgraph}
  {u v w : V}
-- given
  (hMstar' : Mstar'.IsMatching)
  (hAdj : Mstar'.Adj u v)
  (hGvw : G.Adj v w)
  (hw_fresh : w ∉ Mstar'.verts)
  (hfin : Mstar'.edgeSet.Finite)
  (hvw_notMstar : s(v, w) ∉ Mstar'.edgeSet) :
-- imply
  (matchingSwapEdge Mstar' u v w hMstar' hAdj hGvw hw_fresh).edgeSet.ncard = Mstar'.edgeSet.ncard := by
-- proof
  have hEdgeSet : (matchingSwapEdge Mstar' u v w hMstar' hAdj hGvw hw_fresh).edgeSet =
    (Mstar'.edgeSet \ {s(u, v)}) ∪ {s(v, w)} := by
    ext e; simp only [Subgraph.mem_edgeSet, matchingSwapEdge, Set.mem_union, Set.mem_diff,
      Set.mem_singleton_iff]
    constructor
    · intro h; induction e using Sym2.ind with
      | h a b =>
        obtain ⟨hadj, hne1, hne2⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
        · left; refine ⟨Subgraph.mem_edgeSet.mpr hadj, ?_⟩
          intro heq
          obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp heq
          · exact hne1 ⟨h1, h2⟩
          · exact hne2 ⟨h1, h2⟩
        · right; rfl
        · right; exact Sym2.eq_swap
    · intro h; induction e using Sym2.ind with
      | h a b =>
        obtain ⟨hMstar, hne⟩ | heq := h
        · left
          have hadj := Subgraph.mem_edgeSet.mp hMstar
          refine ⟨hadj, ?_, ?_⟩
          · intro ⟨rfl, rfl⟩; exact hne rfl
          · intro ⟨rfl, rfl⟩; exact hne Sym2.eq_swap
        · rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · right; left; exact ⟨rfl, rfl⟩
          · right; right; exact ⟨rfl, rfl⟩
  rw [hEdgeSet]
  have huv_mem : s(u, v) ∈ Mstar'.edgeSet := Subgraph.mem_edgeSet.mpr hAdj
  have hvw_nmem : s(v, w) ∉ Mstar'.edgeSet \ {s(u, v)} := by
    intro ⟨h, _⟩; exact hvw_notMstar h
  have hfin_diff_uv : (Mstar'.edgeSet \ {s(u, v)}).Finite := hfin.subset Set.diff_subset
  rw [Set.ncard_union_eq (Set.disjoint_singleton_right.mpr hvw_nmem)
    hfin_diff_uv (Set.finite_singleton _),
    Set.ncard_singleton, Set.ncard_diff_singleton_of_mem huv_mem]
  have : 0 < Mstar'.edgeSet.ncard := (Set.ncard_pos hfin).mpr ⟨_, huv_mem⟩
  omega

end SimpleGraph

namespace SimpleGraph

/--
[matchingSwapEdge_diff_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Berge.lean)
-/
@[path]
lemma matchingSwapEdge_diff_le
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableEq V]
  {G : SimpleGraph V}
  {M Mstar' : G.Subgraph}
  {u v w : V}
-- given
  (hMstar' : Mstar'.IsMatching)
  (hAdj : Mstar'.Adj u v)
  (hGvw : G.Adj v w)
  (hw_fresh : w ∉ Mstar'.verts)
  (huv_notM : s(u, v) ∉ M.edgeSet)
  (hvw_inM : s(v, w) ∈ M.edgeSet)
  (hfin : Mstar'.edgeSet.Finite)
  (hn : (Mstar'.edgeSet \ M.edgeSet).ncard ≤ n + 1) :
-- imply
  ((matchingSwapEdge Mstar' u v w hMstar' hAdj hGvw hw_fresh).edgeSet \ M.edgeSet).ncard ≤ n := by
-- proof
  have hvw_notMstar : s(v, w) ∉ Mstar'.edgeSet := by
    intro hmem; exact hw_fresh (Subgraph.mem_edgeSet.mp hmem).snd_mem
  have hEdgeSet : (matchingSwapEdge Mstar' u v w hMstar' hAdj hGvw hw_fresh).edgeSet =
    (Mstar'.edgeSet \ {s(u, v)}) ∪ {s(v, w)} := by
    ext e; simp only [Subgraph.mem_edgeSet, matchingSwapEdge, Set.mem_union, Set.mem_diff,
      Set.mem_singleton_iff]
    constructor
    · intro h; induction e using Sym2.ind with
      | h a b =>
        obtain ⟨hadj, hne1, hne2⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
        · left; exact ⟨Subgraph.mem_edgeSet.mpr hadj, fun heq =>
          (Sym2.eq_iff.mp heq).elim (fun ⟨h1, h2⟩ => hne1 ⟨h1, h2⟩)
            (fun ⟨h1, h2⟩ => hne2 ⟨h1, h2⟩)⟩
        · right; rfl
        · right; exact Sym2.eq_swap
    · intro h; induction e using Sym2.ind with
      | h a b =>
        obtain ⟨hMstar, hne⟩ | heq := h
        · have hadj := Subgraph.mem_edgeSet.mp hMstar
          exact Or.inl ⟨hadj, fun ⟨rfl, rfl⟩ => hne rfl, fun ⟨rfl, rfl⟩ => hne Sym2.eq_swap⟩
        · rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  have hsub : (matchingSwapEdge Mstar' u v w hMstar' hAdj hGvw hw_fresh).edgeSet \ M.edgeSet ⊆
    (Mstar'.edgeSet \ M.edgeSet) \ {s(u, v)} := by
    rw [hEdgeSet]
    intro e ⟨he_swap, he_notM⟩
    obtain ⟨he_Mstar, he_ne_uv⟩ | he_vw := he_swap
    · exact ⟨⟨he_Mstar, he_notM⟩, he_ne_uv⟩
    · exact absurd (Set.mem_singleton_iff.mp he_vw ▸ hvw_inM) he_notM
  have huv_inDiff : s(u, v) ∈ Mstar'.edgeSet \ M.edgeSet :=
    ⟨Subgraph.mem_edgeSet.mpr hAdj, huv_notM⟩
  have hfin_diff : (Mstar'.edgeSet \ M.edgeSet).Finite := hfin.subset Set.diff_subset
  calc ((matchingSwapEdge Mstar' u v w hMstar' hAdj hGvw hw_fresh).edgeSet \ M.edgeSet).ncard
    ≤ ((Mstar'.edgeSet \ M.edgeSet) \ {s(u, v)}).ncard :=
      Set.ncard_le_ncard hsub (hfin_diff.subset Set.diff_subset)
    _ = (Mstar'.edgeSet \ M.edgeSet).ncard - 1 :=
      Set.ncard_diff_singleton_of_mem huv_inDiff
    _ ≤ n := by omega

end SimpleGraph

namespace SimpleGraph

/--
[not_isMaxMatching_of_hasAugmentingPath](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Berge.lean)
-/
@[path]
lemma not_isMaxMatching_of_hasAugmentingPath
  [DecidableEq V]
  {G : SimpleGraph V}
  {M : G.Subgraph}
-- given
  (hM : M.IsMatching)
  (haug : HasAugmentingPath G M) :
-- imply
  ¬ M.IsMaxMatching := by
-- proof
  obtain ⟨u, v, p, hp⟩ := haug
  intro ⟨_, hmax⟩
  obtain ⟨M', hM'match, hM'card⟩ := augmenting_path_gives_larger_matching M hM p hp
  linarith [hmax M' hM'match]

end SimpleGraph


-- created on 2026-10-23
