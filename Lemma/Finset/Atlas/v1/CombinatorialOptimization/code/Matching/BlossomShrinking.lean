import Mathlib
import sympy.Basic
import Def.v1.Atlas.CombinatorialOptimization.code.Matching.BlossomShrinking.Part2
open SimpleGraph


namespace SimpleGraph

/--
[blossomContractMap_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/BlossomShrinking.lean)
-/
@[path]
lemma blossomContractMap_mem
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Finset V}
  {base : V}
  {v : V}
-- given
  (hv : v ∈ B) :
-- imply
  blossomContractMap B base v = base := by
-- proof
  simp [blossomContractMap, hv]

end SimpleGraph

namespace SimpleGraph

/--
[blossomContractMap_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/BlossomShrinking.lean)
-/
@[path]
lemma blossomContractMap_not_mem
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Finset V}
  {base : V}
  {v : V}
-- given
  (hv : v ∉ B) :
-- imply
  blossomContractMap B base v = v := by
-- proof
  simp [blossomContractMap, hv]

end SimpleGraph

namespace SimpleGraph

/--
[inducedMatchingSubgraph_isMatching](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/BlossomShrinking.lean)
-/
@[path]
lemma inducedMatchingSubgraph_isMatching
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : G.Subgraph}
  {B : Finset V}
  {base : V}
-- given
  (hM : M.IsMatching)
  (hB : IsBlossom G M B base) :
-- imply
  (inducedMatchingSubgraph M B base).IsMatching := by
-- proof
  intro v hv
  simp only [inducedMatchingSubgraph] at hv ⊢
  obtain ⟨a, ha_mem, ha_eq⟩ := hv
  obtain ⟨w, hw_adj, hw_unique⟩ := hM ha_mem
  by_cases haB : a ∈ B
  ·
    subst ha_eq
    rw [blossomContractMap_mem B base a haB]
    obtain ⟨w_stem, hw_stem_notB, hw_stem_adj⟩ := hB.stem
    have hbase_mem : base ∈ M.verts := M.edge_vert hw_stem_adj
    obtain ⟨w_base, hw_base_adj, hw_base_unique⟩ := hM hbase_mem
    have hw_stem_eq : w_stem = w_base := hw_base_unique w_stem hw_stem_adj
    use blossomContractMap B base w_stem
    constructor
    · constructor
      · rw [blossomContractMap_not_mem B base w_stem hw_stem_notB]
        rw [contractBlossom, map_adj']
        refine ⟨?_, base, w_stem, M.adj_sub hw_stem_adj,
          blossomContractMap_mem B base base hB.base_mem,
          blossomContractMap_not_mem B base w_stem hw_stem_notB⟩
        intro h
        exact hw_stem_notB (h ▸ hB.base_mem)
      · exact ⟨base, w_stem, blossomContractMap_mem B base base hB.base_mem,
        rfl, hw_stem_adj, fun ⟨_, hw⟩ => hw_stem_notB hw⟩
    · intro y ⟨_, c, d, hcu, hdv, hcd_adj, hcd_notB⟩
      have hcB : c ∈ B := by
        by_contra hc
        simp [blossomContractMap_not_mem B base c hc] at hcu
        exact hc (hcu ▸ hB.base_mem)
      have hdnotB : d ∉ B := fun hd => hcd_notB ⟨hcB, hd⟩
      rw [blossomContractMap_not_mem B base d hdnotB] at hdv
      rw [← hdv, blossomContractMap_not_mem B base w_stem hw_stem_notB]
      by_cases hc_base : c = base
      · subst hc_base
        exact (hw_stem_eq ▸ hw_base_unique d hcd_adj)
      · obtain ⟨w', hw'B, _, hw'_adj⟩ := hB.matched_internal c hcB hc_base
        have hc_mem : c ∈ M.verts := M.edge_vert hcd_adj
        obtain ⟨unique_w, h_unique_adj, h_unique⟩ := hM hc_mem
        have hd_eq : d = unique_w := h_unique d hcd_adj
        have hw'_eq : w' = unique_w := h_unique w' hw'_adj
        exfalso
        exact hdnotB (hd_eq ▸ hw'_eq ▸ hw'B)
  ·
    subst ha_eq
    rw [blossomContractMap_not_mem B base a haB]
    use blossomContractMap B base w
    constructor
    · constructor
      · rw [contractBlossom, map_adj']
        constructor
        · intro h
          by_cases hwB : w ∈ B
          · rw [blossomContractMap_mem B base w hwB] at h
            exact haB (h ▸ hB.base_mem)
          · rw [blossomContractMap_not_mem B base w hwB] at h
            exact (M.adj_sub hw_adj).ne h
        · exact ⟨a, w, M.adj_sub hw_adj,
          blossomContractMap_not_mem B base a haB, rfl⟩
      · exact ⟨a, w, blossomContractMap_not_mem B base a haB, rfl, hw_adj,
        fun ⟨ha', _⟩ => haB ha'⟩
    · intro y ⟨_, c, d, hcu, hdv, hcd_adj, hcd_notB⟩
      have hcB_or : c = a := by
        by_cases hcB : c ∈ B
        · rw [blossomContractMap_mem B base c hcB] at hcu
          exact absurd (hcu ▸ hB.base_mem) haB
        · rwa [blossomContractMap_not_mem B base c hcB] at hcu
      subst hcB_or
      have : d = w := hw_unique d hcd_adj
      subst this
      exact hdv.symm

end SimpleGraph

namespace SimpleGraph

/--
[blossom_verts_in_M_verts](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/BlossomShrinking.lean)
-/
@[path]
lemma blossom_verts_in_M_verts
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : G.Subgraph}
  {B : Finset V}
  {base : V}
-- given
  (hB : IsBlossom G M B base) :
-- imply
  ∀ v ∈ B, v ∈ M.verts := by
-- proof
  intro v hv
  by_cases h : v = base
  · subst h
    exact M.edge_vert hB.stem.choose_spec.2
  · obtain ⟨w, _, _, hw_adj⟩ := hB.matched_internal v hv h
    exact M.edge_vert hw_adj

end SimpleGraph

namespace SimpleGraph

/--
[odd_cycle_matching_avoiding_any_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/BlossomShrinking.lean)
-/
@[path]
lemma odd_cycle_matching_avoiding_any_vertex
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  {B : Finset V}
  {base : V}
  {c : G.Walk base base}
  {v : V}
-- given
  (hbase : base ∈ B)
  (hB_odd : Odd B.card)
  (hB_ge : 3 ≤ B.card)
  (hc : c.IsCycle)
  (hsupp : c.support.toFinset = B)
  (hv : v ∈ B) :
-- imply
  ∃ (S : Set (Sym2 V)), S ⊆ G.edgeSet ∧ (∀ e ∈ S, ∀ w ∈ e, w ∈ B ∧ w ≠ v) ∧ S.ncard = (B.card - 1) / 2 ∧ (∀ e₁ ∈ S, ∀ e₂ ∈ S, e₁ ≠ e₂ → Disjoint (e₁ : Set V) e₂) := by
-- proof
  classical
  have hv_supp : v ∈ c.support := List.mem_toFinset.mp (hsupp ▸ hv)
  set c' := c.rotate v hv_supp with hc'_def
  have hc' : c'.IsCycle := hc.rotate hv_supp
  have hlen_eq : c'.length = c.length := by
    simp only [hc'_def, Walk.rotate, Walk.length_append]
    have := Walk.take_spec c hv_supp
    have h1 := congr_arg Walk.length this
    rw [Walk.length_append] at h1; omega
  have hsupp' : c'.support.toFinset = B := by
    ext w; simp only [List.mem_toFinset]
    constructor
    · intro hw
      have := (Walk.mem_support_rotate_iff c v hv_supp).mp hw
      rwa [← List.mem_toFinset, hsupp] at this
    · intro hw
      apply (Walk.mem_support_rotate_iff c v hv_supp).mpr
      rwa [← List.mem_toFinset, hsupp]
  have hcard_len : B.card = c'.length := by
    rw [← hsupp']
    have h_nodup := hc'.support_nodup
    have h_u_in_tail : v ∈ c'.support.tail := by
      cases hc'_eq : c' with
      | nil => exact absurd hc'_eq (by intro h; exact hc'.ne_nil (h ▸ rfl))
      | cons hadj p =>
        simp only [Walk.support, List.tail_cons]
        exact Walk.end_mem_support p
    have h_eq : c'.support.toFinset = c'.support.tail.toFinset := by
      rw [Walk.support_eq_cons c', List.toFinset_cons]
      exact Finset.insert_eq_of_mem (List.mem_toFinset.mpr h_u_in_tail)
    rw [h_eq, List.toFinset_card_of_nodup h_nodup, List.length_tail, Walk.length_support]; omega
  have hlen_ge : 3 ≤ c'.length := hcard_len ▸ hB_ge
  obtain ⟨k, hk⟩ : ∃ k, c'.length = 2 * k + 1 := by
    obtain ⟨k, hk⟩ := (hcard_len ▸ hB_odd); exact ⟨k, by omega⟩
  have hk_pos : k ≥ 1 := by omega
  have getVert_mem_B : ∀ i, c'.getVert i ∈ B := fun i =>
    hsupp' ▸ List.mem_toFinset.mpr (Walk.getVert_mem_support c' i)
  have getVert_ne_v : ∀ i, 1 ≤ i → i < c'.length → c'.getVert i ≠ v := by
    intro i hi1 hi2 heq
    have hinj := hc'.getVert_injOn
    have hi_in : i ∈ {j : ℕ | 1 ≤ j ∧ j ≤ c'.length} := ⟨hi1, le_of_lt hi2⟩
    have hn_in : c'.length ∈ {j : ℕ | 1 ≤ j ∧ j ≤ c'.length} := ⟨by omega, le_refl _⟩
    have h_eq : c'.getVert i = c'.getVert c'.length := by rw [heq, Walk.getVert_length]
    exact absurd (hinj hi_in hn_in h_eq) (by omega)
  let mkEdge (i : Fin k) : Sym2 V :=
    s(c'.getVert (2 * i.val + 1), c'.getVert (2 * i.val + 2))
  have mkEdge_inj : Function.Injective mkEdge := by
    intro i j h_eq
    have hinj := hc'.getVert_injOn
    simp only [mkEdge, Sym2.eq_iff] at h_eq
    obtain ⟨h1, _⟩ | ⟨h1, _⟩ := h_eq
    · have hi : (2 * i.val + 1) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
      constructor <;> omega
      have hj : (2 * j.val + 1) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
        constructor <;> omega
      exact Fin.ext (by have := hinj hi hj h1; omega)
    · have hi : (2 * i.val + 1) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
      constructor <;> omega
      have hj : (2 * j.val + 2) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
        constructor <;> omega
      exact absurd (hinj hi hj h1) (by omega)
  let S : Set (Sym2 V) := Set.range mkEdge
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  ·
    intro e he; obtain ⟨i, rfl⟩ := he
    rw [SimpleGraph.mem_edgeSet]
    exact c'.adj_getVert_succ (by omega : 2 * i.val + 1 < c'.length)
  ·
    intro e he w hw
    obtain ⟨i, rfl⟩ := he
    change w ∈ (mkEdge i : Sym2 V) at hw
    simp only [mkEdge, Sym2.mem_iff] at hw
    obtain rfl | rfl := hw
    · exact ⟨getVert_mem_B _, getVert_ne_v _ (by omega) (by omega)⟩
    · exact ⟨getVert_mem_B _, getVert_ne_v _ (by omega) (by omega)⟩
  ·
    have h_ncard : S.ncard = k := by
      have h1 := Set.ncard_range_of_injective mkEdge_inj
      rwa [Nat.card_fin] at h1
    rw [h_ncard, hcard_len, hk]; omega
  ·
    intro e₁ he₁ e₂ he₂ hne
    obtain ⟨i, rfl⟩ := he₁
    obtain ⟨j, rfl⟩ := he₂
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    rw [Set.disjoint_left]
    intro w hw₁ hw₂
    change w ∈ (mkEdge i : Sym2 V) at hw₁
    change w ∈ (mkEdge j : Sym2 V) at hw₂
    simp only [mkEdge, Sym2.mem_iff] at hw₁ hw₂
    have hinj := hc'.getVert_injOn
    have h_i1 : (2 * i.val + 1) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
      constructor <;> omega
    have h_i2 : (2 * i.val + 2) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
      constructor <;> omega
    have h_j1 : (2 * j.val + 1) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
      constructor <;> omega
    have h_j2 : (2 * j.val + 2) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
      constructor <;> omega
    obtain rfl | rfl <;> rcases hw₂ with h | h := hw₁
    · exact absurd (hinj h_i1 h_j1 h) (by omega)
    · exact absurd (hinj h_i1 h_j2 h) (by omega)
    · exact absurd (hinj h_i2 h_j1 h) (by omega)
    · exact absurd (hinj h_i2 h_j2 h) (by omega)

end SimpleGraph

namespace SimpleGraph

/--
[induced_matching_edgeSet_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/BlossomShrinking.lean)
-/
@[path]
lemma induced_matching_edgeSet_ncard
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : G.Subgraph}
  {B : Finset V}
  {base : V}
-- given
  (hM : M.IsMatching)
  (hB : IsBlossom G M B base) :
-- imply
  M.edgeSet.ncard = (inducedMatchingSubgraph M B base).edgeSet.ncard + (B.card - 1) / 2 := by
-- proof
  have hM_fin : M.edgeSet.Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  have hM'_fin : (inducedMatchingSubgraph M B base).edgeSet.Finite :=
    Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  have hM' : (inducedMatchingSubgraph M B base).IsMatching :=
    inducedMatchingSubgraph_isMatching M hM B base hB
  have hM_eq := matching_verts_twice_edges hM hM_fin
  have hM'_eq := matching_verts_twice_edges hM' hM'_fin
  have hB_sub : (↑B : Set V) ⊆ M.verts :=
    fun v hv => blossom_verts_in_M_verts M B base hB v hv
  have hM_verts_fin : M.verts.Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  have h_M_decomp : M.verts.ncard = (M.verts \ ↑B).ncard + B.card := by
    have := Set.ncard_diff_add_ncard_of_subset hB_sub hM_verts_fin
    rw [Set.ncard_coe_finset] at this; omega
  have h_verts_eq : (inducedMatchingSubgraph M B base).verts = (M.verts \ ↑B) ∪ {base} := by
    ext v
    simp only [inducedMatchingSubgraph, Set.mem_image, Set.mem_union, Set.mem_diff,
      Set.mem_singleton_iff, Finset.mem_coe]
    constructor
    · rintro ⟨a, ha_mem, ha_eq⟩
      by_cases haB : a ∈ B
      · have : blossomContractMap B base a = base := by simp [blossomContractMap, haB]
        rw [this] at ha_eq; right; exact ha_eq.symm
      · have : blossomContractMap B base a = a := by simp [blossomContractMap, haB]
        rw [this] at ha_eq; subst ha_eq; left; exact ⟨ha_mem, haB⟩
    · intro h
      obtain ⟨hv_mem, hv_notB⟩ | hv_eq := h
      · exact ⟨v, hv_mem, by simp [blossomContractMap, hv_notB]⟩
      · exact ⟨base, hB_sub hB.base_mem, by simp [blossomContractMap, hB.base_mem, hv_eq]⟩
  have h_M'_decomp : (inducedMatchingSubgraph M B base).verts.ncard =
    (M.verts \ ↑B).ncard + 1 := by
    rw [h_verts_eq]
    have hbase_not : base ∉ (M.verts \ (↑B : Set V)) := by
      simp [Set.mem_diff]; intro _; exact hB.base_mem
    have h_disj : Disjoint (M.verts \ ↑B) ({base} : Set V) :=
      Set.disjoint_singleton_right.mpr hbase_not
    rw [Set.ncard_union_eq h_disj (hM_verts_fin.subset Set.diff_subset)
      (Set.finite_singleton _), Set.ncard_singleton]
  obtain ⟨k, hk⟩ := hB.card_odd
  omega

end SimpleGraph

namespace SimpleGraph

/--
[walk_edges_in_contractBlossom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/BlossomShrinking.lean)
-/
@[path]
lemma walk_edges_in_contractBlossom
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {B : Finset V}
  {base : V}
  {u v : V}
  {p : G.Walk u v}
-- given
  (hdisjoint : ∀ w ∈ p.support, w ∉ B) :
-- imply
  ∀ e ∈ p.edges, e ∈ (contractBlossom G B base).edgeSet := by
-- proof
  intro e he
  have hedge := p.edges_subset_edgeSet he
  revert he hedge
  apply Sym2.ind (f := fun e => e ∈ p.edges → e ∈ G.edgeSet →
    e ∈ (contractBlossom G B base).edgeSet)
  intro a b he hedge
  have hadj : G.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at hedge
  have ha : a ∉ B := hdisjoint a (Walk.fst_mem_support_of_mem_edges p he)
  have hb : b ∉ B := hdisjoint b (Walk.snd_mem_support_of_mem_edges p he)
  rw [SimpleGraph.mem_edgeSet]
  show (contractBlossom G B base).Adj a b
  rw [contractBlossom, map_adj']
  exact ⟨hadj.ne, a, b, hadj, by simp [blossomContractMap, ha], by simp [blossomContractMap, hb]⟩

end SimpleGraph

namespace SimpleGraph

/--
[inducedMatching_adj_iff_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/BlossomShrinking.lean)
-/
@[path]
lemma inducedMatching_adj_iff_of_not_mem
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : G.Subgraph}
  {B : Finset V}
  {base : V}
  {a b : V}
-- given
  (hbase : base ∈ B)
  (ha : a ∉ B)
  (hb : b ∉ B)
  (hadj_G : G.Adj a b) :
-- imply
  (inducedMatchingSubgraph M B base).Adj a b ↔ M.Adj a b := by
-- proof
  constructor
  · intro ⟨_, c, d, hc, hd, hcd_adj, _⟩
    have hcB : c ∉ B := by
      intro hcB; simp [blossomContractMap, hcB] at hc; exact ha (hc ▸ hbase)
    simp [blossomContractMap, hcB] at hc
    have hdB : d ∉ B := by
      intro hdB; simp [blossomContractMap, hdB] at hd; exact hb (hd ▸ hbase)
    simp [blossomContractMap, hdB] at hd
    rw [← hc, ← hd]; exact hcd_adj
  · intro hab
    refine ⟨?_, a, b, ?_, ?_, hab, fun ⟨ha', _⟩ => ha ha'⟩
    · rw [contractBlossom, map_adj']
      exact ⟨hadj_G.ne, a, b, hadj_G,
        by simp [blossomContractMap, ha], by simp [blossomContractMap, hb]⟩
    · simp [blossomContractMap, ha]
    · simp [blossomContractMap, hb]

end SimpleGraph

namespace SimpleGraph

/--
[inducedMatching_edgeSet_iff_of_support_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/BlossomShrinking.lean)
-/
@[path]
lemma inducedMatching_edgeSet_iff_of_support_disjoint
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : G.Subgraph}
  {B : Finset V}
  {base : V}
  {u v : V}
  {p : G.Walk u v}
  {e : Sym2 V}
-- given
  (hbase : base ∈ B)
  (hdisjoint : ∀ w ∈ p.support, w ∉ B)
  (he : e ∈ p.edges) :
-- imply
  e ∈ (inducedMatchingSubgraph M B base).edgeSet ↔ e ∈ M.edgeSet := by
-- proof
  revert he
  apply Sym2.ind (f := fun e => e ∈ p.edges →
    (e ∈ (inducedMatchingSubgraph M B base).edgeSet ↔ e ∈ M.edgeSet))
  intro a b he
  have ha : a ∉ B := hdisjoint a (Walk.fst_mem_support_of_mem_edges p he)
  have hb : b ∉ B := hdisjoint b (Walk.snd_mem_support_of_mem_edges p he)
  have hadj_G : G.Adj a b := by
    have := p.edges_subset_edgeSet he
    rwa [SimpleGraph.mem_edgeSet] at this
  rw [Subgraph.mem_edgeSet, Subgraph.mem_edgeSet]
  exact inducedMatching_adj_iff_of_not_mem M B base hbase ha hb hadj_G

end SimpleGraph

namespace SimpleGraph

/--
[unmatched_not_in_induced_verts](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/BlossomShrinking.lean)
-/
@[path]
lemma unmatched_not_in_induced_verts
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : G.Subgraph}
  {B : Finset V}
  {base : V}
  {w : V}
-- given
  (hbase : base ∈ B)
  (hM : M.IsMatching)
  (hB : IsBlossom G M B base)
  (hw : w ∉ M.verts)
  (hwB : w ∉ B) :
-- imply
  w ∉ (inducedMatchingSubgraph M B base).verts := by
-- proof
  simp only [inducedMatchingSubgraph]
  intro ⟨a, ha_mem, ha_eq⟩
  by_cases haB : a ∈ B
  · simp [blossomContractMap, haB] at ha_eq
    exact hwB (ha_eq ▸ hbase)
  · simp [blossomContractMap, haB] at ha_eq
    exact hw (ha_eq ▸ ha_mem)

end SimpleGraph


-- created on 2026-10-23
