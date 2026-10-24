import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Matching.EdmondsRuntime
open SimpleGraph


namespace SimpleGraph

/--
[matching_edgeSet_ncard_le_card_div_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean)
-/
@[path]
lemma matching_edgeSet_ncard_le_card_div_two
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : G.Subgraph}
-- given
  (hM : M.IsMatching) :
-- imply
  M.edgeSet.ncard ≤ Fintype.card V / 2 := by
-- proof
  classical
  suffices h : 2 * M.edgeSet.ncard ≤ Fintype.card V by omega
  have hverts_le : M.verts.ncard ≤ Fintype.card V := by
    have h := Set.ncard_le_ncard (s := M.verts) (t := Set.univ)
      (Set.subset_univ _) Set.finite_univ
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h
  suffices h2 : 2 * M.edgeSet.ncard ≤ M.verts.ncard from le_trans h2 hverts_le
  rw [Set.ncard_eq_toFinset_card' M.edgeSet, Set.ncard_eq_toFinset_card' M.verts]
  have hbiUnion_sub : M.edgeSet.toFinset.biUnion sym2Endpoints ⊆ M.verts.toFinset := by
    intro v hv
    simp only [Finset.mem_biUnion] at hv
    obtain ⟨e, he, hve⟩ := hv
    rw [Set.mem_toFinset] at he
    simp only [sym2Endpoints, Multiset.mem_toFinset, Sym2.mem_toMultiset] at hve
    rw [Set.mem_toFinset]
    induction e using Sym2.ind with
    | h a b =>
      rw [Subgraph.mem_edgeSet] at he
      rw [Sym2.mem_iff] at hve
      obtain rfl | rfl := hve
      · exact M.edge_vert he
      · exact M.edge_vert (M.adj_symm he)
  have hpwd : ∀ e₁ ∈ M.edgeSet.toFinset, ∀ e₂ ∈ M.edgeSet.toFinset,
    e₁ ≠ e₂ → Disjoint (sym2Endpoints e₁) (sym2Endpoints e₂) := by
    intro e₁ he₁ e₂ he₂ hne
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    simp only [sym2Endpoints, Multiset.mem_toFinset, Sym2.mem_toMultiset] at hv₁ hv₂
    rw [Set.mem_toFinset] at he₁ he₂
    have hv_verts : v ∈ M.verts := by
      induction e₁ using Sym2.ind with
      | h a b =>
        rw [Subgraph.mem_edgeSet] at he₁
        rw [Sym2.mem_iff] at hv₁
        obtain rfl | rfl := hv₁
        · exact M.edge_vert he₁
        · exact M.edge_vert (M.adj_symm he₁)
    obtain ⟨w, hw, huniq⟩ := hM hv_verts
    have he₁_eq : e₁ = s(v, w) := by
      induction e₁ using Sym2.ind with
      | h a b =>
        rw [Subgraph.mem_edgeSet] at he₁
        rw [Sym2.mem_iff] at hv₁
        obtain rfl | rfl := hv₁
        · congr 1; exact huniq b he₁
        · rw [huniq a (M.adj_symm he₁)]; exact Sym2.eq_swap
    have he₂_eq : e₂ = s(v, w) := by
      induction e₂ using Sym2.ind with
      | h a b =>
        rw [Subgraph.mem_edgeSet] at he₂
        rw [Sym2.mem_iff] at hv₂
        obtain rfl | rfl := hv₂
        · congr 1; exact huniq b he₂
        · rw [huniq a (M.adj_symm he₂)]; exact Sym2.eq_swap
    exact hne (he₁_eq.trans he₂_eq.symm)
  have hcard2 : ∀ e ∈ M.edgeSet.toFinset, (sym2Endpoints e).card = 2 := by
    intro e he
    rw [Set.mem_toFinset] at he
    induction e using Sym2.ind with
    | h a b =>
      rw [Subgraph.mem_edgeSet] at he
      have hab : a ≠ b := fun heq => (M.adj_sub he).ne (heq ▸ rfl)
      simp [sym2Endpoints, Sym2.toMultiset]
      exact Finset.card_pair hab
  have hcard_biUnion : (M.edgeSet.toFinset.biUnion sym2Endpoints).card =
    2 * M.edgeSet.toFinset.card := by
    rw [Finset.card_biUnion hpwd]
    simp only [Finset.sum_congr rfl hcard2, Finset.sum_const, smul_eq_mul, mul_comm]
  calc 2 * M.edgeSet.toFinset.card
    = (M.edgeSet.toFinset.biUnion sym2Endpoints).card := hcard_biUnion.symm
    _ ≤ M.verts.toFinset.card := Finset.card_le_card hbiUnion_sub

end SimpleGraph

namespace SimpleGraph

/--
[fin_seq_le_last](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean)
-/
@[path]
lemma fin_seq_le_last
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ℕ}
  {f : Fin (n + 1) → ℕ}
-- given
  (hinc : ∀ i : Fin n, f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ = f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ + 1) :
-- imply
  n ≤ f ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ := by
-- proof
  suffices h : ∀ k (hk : k ≤ n), k ≤ f ⟨k, Nat.lt_succ_iff.mpr hk⟩ from h n le_rfl
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    have hk_lt_n : k < n := Nat.lt_of_succ_le hk
    have h_inc := hinc ⟨k, hk_lt_n⟩
    have h_eq : f ⟨k + 1, Nat.lt_succ_iff.mpr hk⟩ = f ⟨k + 1, Nat.succ_lt_succ hk_lt_n⟩ := by
      congr 1
    rw [h_eq, h_inc]
    have := ih hk'
    have h_eq2 : f ⟨k, Nat.lt_succ_iff.mpr hk'⟩ = f ⟨k, Nat.lt_succ_of_lt hk_lt_n⟩ := by
      congr 1
    linarith [h_eq2 ▸ this]

end SimpleGraph

namespace SimpleGraph

/--
[edmonds_phase_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean)
-/
@[path]
lemma edmonds_phase_bound
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {exec : EdmondsExecution G} :
-- imply
  exec.numPhases ≤ Fintype.card V / 2 := by
-- proof
  have h1 : exec.numPhases ≤
    (exec.matching ⟨exec.numPhases, Nat.lt_succ_of_le le_rfl⟩).edgeSet.ncard := by
    exact fin_seq_le_last
      (fun i => (exec.matching i).edgeSet.ncard)
      exec.size_increases_by_one
  have h2 : (exec.matching ⟨exec.numPhases, Nat.lt_succ_of_le le_rfl⟩).edgeSet.ncard ≤
    Fintype.card V / 2 :=
    matching_edgeSet_ncard_le_card_div_two _ (exec.isFinalMaximum.1)
  exact le_trans h1 h2

end SimpleGraph

namespace SimpleGraph

/--
[contractions_bound_of_vertex_reduction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean)
-/
@[path]
lemma contractions_bound_of_vertex_reduction
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : ℕ}
  {f : Fin (k + 1) → ℕ}
  {n : ℕ}
-- given
  (hinit : f ⟨0, Nat.zero_lt_succ _⟩ ≤ n)
  (hdecr : ∀ i : Fin k, f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ + 2 ≤ f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) :
-- imply
  k ≤ n / 2 := by
-- proof
  suffices h : 2 * k ≤ n by omega
  suffices h2 : 2 * k ≤ f ⟨0, Nat.zero_lt_succ _⟩ from le_trans h2 hinit
  suffices h3 : ∀ j (hj : j ≤ k),
    f ⟨0, Nat.zero_lt_succ _⟩ ≥ f ⟨j, Nat.lt_succ_iff.mpr hj⟩ + 2 * j from by
    have := h3 k le_rfl; omega
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hj' : j ≤ k := Nat.le_of_succ_le hj
    have hj_lt : j < k := Nat.lt_of_succ_le hj
    have ih_val := ih hj'
    have hdecr_j := hdecr ⟨j, hj_lt⟩
    have h_eq1 : f ⟨j, Nat.lt_succ_iff.mpr hj'⟩ = f ⟨j, Nat.lt_succ_of_lt hj_lt⟩ := by congr 1
    have h_eq2 : f ⟨j + 1, Nat.lt_succ_iff.mpr hj⟩ =
      f ⟨j + 1, Nat.succ_lt_succ hj_lt⟩ := by congr 1
    linarith [h_eq1 ▸ ih_val, h_eq2 ▸ hdecr_j]

end SimpleGraph

namespace SimpleGraph

/--
[edmonds_total_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean)
-/
@[path]
lemma edmonds_total_bound
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {exec : EdmondsExecution G} :
-- imply
  exec.numPhases * G.edgeFinset.card * (Fintype.card V / 2 + 1) ≤ Fintype.card V / 2 * G.edgeFinset.card * Fintype.card V := by
-- proof
  have h := edmonds_phase_bound exec
  have key : Fintype.card V / 2 * (Fintype.card V / 2 + 1) ≤
    Fintype.card V / 2 * Fintype.card V := by
    cases hn : Fintype.card V with
    | zero => simp
    | succ k =>
      cases k with
      | zero => simp
      | succ j =>
        apply Nat.mul_le_mul_left
        omega
  calc exec.numPhases * G.edgeFinset.card * (Fintype.card V / 2 + 1)
    = exec.numPhases * (Fintype.card V / 2 + 1) * G.edgeFinset.card := by ring
    _ ≤ (Fintype.card V / 2) * (Fintype.card V / 2 + 1) * G.edgeFinset.card := by
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_right
      exact h
    _ ≤ Fintype.card V / 2 * Fintype.card V * G.edgeFinset.card := by
      apply Nat.mul_le_mul_right
      exact key
    _ = Fintype.card V / 2 * G.edgeFinset.card * Fintype.card V := by ring

end SimpleGraph

namespace SimpleGraph

/--
[symmDiff_edgeSet_ncard_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean)
-/
@[path]
lemma symmDiff_edgeSet_ncard_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq V]
  {G : SimpleGraph V}
  {M : G.Subgraph}
  {u v : V}
  {p : G.Walk u v}
-- given
  (hM : M.IsMatching)
  (haug : p.IsAugmentingPath M)
  (hfin : M.edgeSet.Finite) :
-- imply
  (symmDiffMatching M p).edgeSet.ncard = M.edgeSet.ncard + 1 := by
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
[subgraph_edgeSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean)
-/
@[path]
lemma subgraph_edgeSet_finite
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : G.Subgraph} :
-- imply
  M.edgeSet.Finite :=
-- proof
  M.edgeSet.toFinite

end SimpleGraph

namespace SimpleGraph

/--
[exists_matching_succ_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean)
-/
@[path]
lemma exists_matching_succ_ncard
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : G.Subgraph}
-- given
  (hM : M.IsMatching)
  (hnmax : ¬ Subgraph.IsMaxMatching M) :
-- imply
  ∃ M' : G.Subgraph, M'.IsMatching ∧ M'.edgeSet.ncard = M.edgeSet.ncard + 1 := by
-- proof
  classical
  have haug := hasAugmentingPath_of_not_isMaxMatching M hM (subgraph_edgeSet_finite M) hnmax
  obtain ⟨u, v, p, hp⟩ := haug
  exact ⟨symmDiffMatching M p,
    symmDiffMatching_isMatching M hM p hp,
    symmDiff_edgeSet_ncard_eq M hM p hp (subgraph_edgeSet_finite M)⟩

end SimpleGraph

namespace SimpleGraph

/--
[exists_max_matching](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean)
-/
@[path]
lemma exists_max_matching
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ M : G.Subgraph, Subgraph.IsMaxMatching M := by
-- proof
  classical
  by_contra h
  push_neg at h
  have hbot : (⊥ : G.Subgraph).IsMatching := by
    intro v hv; simp [Subgraph.verts_bot] at hv
  have step : ∀ M : G.Subgraph, M.IsMatching →
    ∃ M' : G.Subgraph, M'.IsMatching ∧ M.edgeSet.ncard < M'.edgeSet.ncard := by
    intro M hM
    have hnmax := h M
    unfold Subgraph.IsMaxMatching at hnmax
    push_neg at hnmax
    obtain ⟨M', hM', hcard⟩ := hnmax hM
    exact ⟨M', hM', hcard⟩
  have build : ∀ n : ℕ, ∃ M : G.Subgraph, M.IsMatching ∧ n ≤ M.edgeSet.ncard := by
    intro n
    induction n with
    | zero => exact ⟨⊥, hbot, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨Mk, hMk, hcard_k⟩ := ih
      obtain ⟨M', hM', hcard'⟩ := step Mk hMk
      exact ⟨M', hM', by omega⟩
  obtain ⟨M, hM, hcard⟩ := build (Fintype.card V / 2 + 1)
  linarith [matching_edgeSet_ncard_le_card_div_two M hM]

end SimpleGraph

namespace SimpleGraph

/--
[exists_matching_of_size](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean)
-/
@[path]
lemma exists_matching_of_size
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {Mmax : G.Subgraph}
  {k : ℕ}
-- given
  (hMmax : Subgraph.IsMaxMatching Mmax)
  (hk : k ≤ Mmax.edgeSet.ncard) :
-- imply
  ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k := by
-- proof
  classical
  induction k with
  | zero =>
    refine ⟨⊥, ?_, ?_⟩
    · intro v hv; simp [Subgraph.verts_bot] at hv
    · simp [Subgraph.edgeSet_bot]
  | succ j ih =>
    have hj_le : j ≤ Mmax.edgeSet.ncard := Nat.le_of_succ_le hk
    obtain ⟨Mj, hMj_match, hMj_card⟩ := ih hj_le
    have hnmax : ¬ Subgraph.IsMaxMatching Mj := by
      intro ⟨_, hMj_max⟩
      have := hMj_max Mmax hMmax.1
      omega
    obtain ⟨M', hM', hM'_card⟩ := exists_matching_succ_ncard Mj hMj_match hnmax
    exact ⟨M', hM', by omega⟩

end SimpleGraph

namespace SimpleGraph

/--
[edmonds_execution_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean)
-/
@[path]
lemma edmonds_execution_exists
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ exec : EdmondsExecution G, exec.numPhases ≤ Fintype.card V / 2 := by
-- proof
  classical
  obtain ⟨Mmax, hMmax⟩ := exists_max_matching G
  set t := Mmax.edgeSet.ncard with ht_def
  have ht_le : t ≤ Fintype.card V / 2 := matching_edgeSet_ncard_le_card_div_two Mmax hMmax.1
  have hchoice : ∀ k : Fin (t + 1),
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k.val := by
    intro ⟨k, hk⟩
    exact exists_matching_of_size G Mmax hMmax k (by omega)
  choose seq hseq_match hseq_card using hchoice
  have hseq_inc : ∀ i : Fin t, (seq ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩).edgeSet.ncard =
    (seq ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).edgeSet.ncard + 1 := by
    intro i
    rw [hseq_card ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩,
      hseq_card ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩]
  have hseq_max : Subgraph.IsMaxMatching (seq ⟨t, Nat.lt_succ_of_le le_rfl⟩) := by
    constructor
    · exact hseq_match ⟨t, Nat.lt_succ_of_le le_rfl⟩
    · intro M' hM'
      have hsize := hseq_card ⟨t, Nat.lt_succ_of_le le_rfl⟩
      calc M'.edgeSet.ncard
        ≤ Mmax.edgeSet.ncard := hMmax.2 M' hM'
        _ = t := rfl
        _ = (seq ⟨t, Nat.lt_succ_of_le le_rfl⟩).edgeSet.ncard := hsize.symm
  exact ⟨⟨t, seq, hseq_match, hseq_inc, hseq_max⟩, ht_le⟩

end SimpleGraph

namespace SimpleGraph

/--
[edmonds_algorithm_runtime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean)
-/
@[path]
lemma edmonds_algorithm_runtime
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ (M : G.Subgraph), Subgraph.IsMaxMatching M ∧ ∃ (numPhases : ℕ), numPhases ≤ Fintype.card V / 2 ∧ numPhases * G.edgeFinset.card * (Fintype.card V / 2 + 1) ≤ Fintype.card V / 2 * G.edgeFinset.card * Fintype.card V := by
-- proof
  obtain ⟨exec, hbound⟩ := edmonds_execution_exists G
  refine ⟨exec.matching ⟨exec.numPhases, Nat.lt_succ_of_le le_rfl⟩, exec.isFinalMaximum,
    exec.numPhases, hbound, ?_⟩
  exact edmonds_total_bound exec

end SimpleGraph


-- created on 2026-10-23
