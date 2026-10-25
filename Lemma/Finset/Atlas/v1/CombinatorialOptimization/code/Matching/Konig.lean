import Mathlib
import sympy.Basic
import Def.v1.Atlas.CombinatorialOptimization.code.Matching.Konig
open SimpleGraph Set


namespace SimpleGraph

/--
[mem_edgeSet_adj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Konig.lean)
-/
@[path]
lemma mem_edgeSet_adj
  [DecidableEq V]
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  {M : G.Subgraph}
  {v : V}
  {e : Sym2 V}
-- given
  (he : e ∈ M.edgeSet)
  (hve : v ∈ e) :
-- imply
  ∃ w, M.Adj v w ∧ e = s(v, w) := by
-- proof
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Subgraph.edgeSet, Sym2.fromRel_prop] at he
    simp only [Sym2.mem_iff] at hve
    obtain rfl | rfl := hve
    · exact ⟨b, he, rfl⟩
    · exact ⟨a, he.symm, Sym2.eq_swap⟩

end SimpleGraph

namespace SimpleGraph

/--
[Subgraph.IsMatching.edgeSet_encard_le_of_isVertexCover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Konig.lean)
-/
@[path]
lemma Subgraph.IsMatching.edgeSet_encard_le_of_isVertexCover
  [DecidableEq V]
  {G : SimpleGraph V}
  {M : G.Subgraph}
  {C : Set V}
-- given
  (hM : M.IsMatching)
  (hC : G.IsVertexCover C) :
-- imply
  M.edgeSet.encard ≤ C.encard := by
-- proof
  classical
  have h_endpt : ∀ e ∈ M.edgeSet, ∃ v : V, v ∈ C ∧ v ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ v w =>
      simp only [Subgraph.edgeSet, Sym2.fromRel_prop] at he
      obtain hv | hw := hC (M.adj_sub he)
      · exact ⟨v, hv, Sym2.mem_mk_left v w⟩
      · exact ⟨w, hw, Sym2.mem_mk_right v w⟩
  let f : Sym2 V → V := fun e =>
    if h : e ∈ M.edgeSet then (h_endpt e h).choose else e.out.1
  have hf_maps : MapsTo f M.edgeSet C := by
    intro e he; simp only [f, dif_pos he]; exact (h_endpt e he).choose_spec.1
  have hf_inj : InjOn f M.edgeSet := by
    intro e₁ he₁ e₂ he₂ hfeq
    simp only [f, dif_pos he₁, dif_pos he₂] at hfeq
    have hv₁_in := (h_endpt e₁ he₁).choose_spec.2
    have hv₂_in := (h_endpt e₂ he₂).choose_spec.2
    obtain ⟨w₁, hadj₁, heq₁⟩ := mem_edgeSet_adj M he₁ hv₁_in
    obtain ⟨w₂, hadj₂, heq₂⟩ := mem_edgeSet_adj M he₂ (hfeq ▸ hv₂_in)
    have := hM.eq_of_adj_left hadj₁ hadj₂
    rw [heq₁, heq₂, this]
  exact Set.encard_le_encard_of_injOn hf_maps hf_inj

end SimpleGraph

namespace SimpleGraph

/--
[matchingNum_le_vertexCoverNum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Konig.lean)
-/
@[path]
lemma matchingNum_le_vertexCoverNum
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  G.matchingNum ≤ G.vertexCoverNum := by
-- proof
  apply iSup_le; intro M; apply iSup_le; intro hM
  apply le_iInf; intro C; apply le_iInf; intro hC
  exact hM.edgeSet_encard_le_of_isVertexCover hC

end SimpleGraph

namespace SimpleGraph

/--
[unmatched_A_in_forest](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Konig.lean)
-/
@[path]
lemma unmatched_A_in_forest
  [DecidableEq V]
  {G : SimpleGraph V}
  {M : G.Subgraph}
  {A : Set V}
  {v : V}
-- given
  (hvA : v ∈ A)
  (hvM : v ∉ M.verts) :
-- imply
  IsInAlternatingForest G M A v :=
-- proof
  ⟨v, Walk.nil, hvA, hvM, Walk.IsPath.nil, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

end SimpleGraph

namespace SimpleGraph

/--
[Walk.edges_takeUntil_isPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Konig.lean)
-/
@[path]
lemma Walk.edges_takeUntil_isPrefix
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v w : V}
  {p : G.Walk u v}
-- given
  (hw : w ∈ p.support) :
-- imply
  (p.takeUntil w hw).edges <+: p.edges := by
-- proof
  have heq := congr_arg Walk.edges (Walk.take_spec p hw)
  rw [Walk.edges_append] at heq
  exact ⟨(p.dropUntil w hw).edges, heq⟩

end SimpleGraph

namespace SimpleGraph

/--
[alternatingFrom_takeUntil](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Konig.lean)
-/
@[path]
lemma alternatingFrom_takeUntil
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v w : V}
  {p : G.Walk u v}
  {M : G.Subgraph}
-- given
  (halt : p.IsAlternatingFrom M)
  (hw : w ∈ p.support) :
-- imply
  (p.takeUntil w hw).IsAlternatingFrom M := by
-- proof
  intro i hi
  have hpref := Walk.edges_takeUntil_isPrefix p hw
  have hi' : i < p.edges.length := Nat.lt_of_lt_of_le hi (List.IsPrefix.length_le hpref)
  have hget : (p.takeUntil w hw).edges[i]'hi = p.edges[i]'hi' :=
    List.IsPrefix.getElem hpref hi
  rw [hget]
  exact halt i hi'

end SimpleGraph

namespace SimpleGraph

/--
[forest_edge_not_in_M](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Konig.lean)
-/
@[path]
lemma forest_edge_not_in_M
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Set V}
  {M : G.Subgraph}
  {a v w : V}
  {p : G.Walk a v}
-- given
  (hBip : G.IsBipartiteWith A B)
  (hM : M.IsMatching)
  (haA : a ∈ A)
  (haM : a ∉ M.verts)
  (hvA : v ∈ A)
  (hpath : p.IsPath)
  (halt : p.IsAlternatingFrom M)
  (hadj : G.Adj v w)
  (hw_supp : w ∉ p.support) :
-- imply
  s(v, w) ∉ M.edgeSet := by
-- proof
  intro habs
  rw [Subgraph.mem_edgeSet] at habs
  have hv_matched : v ∈ M.verts := M.edge_vert habs
  have heven : Even p.edges.length := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have := (walk_endpoint_parity hBip p).1 haA |>.2 hodd
    exact absurd hvA (Set.disjoint_left.mp hBip.disjoint.symm this)
  by_cases hp0 : p.edges.length = 0
  · have hav : a = v := p.eq_of_length_eq_zero (by rw [← p.length_edges]; omega)
    rw [← hav] at hv_matched; exact haM hv_matched
  ·
    have hpos : 0 < p.edges.length := Nat.pos_of_ne_zero hp0
    have hlast_idx : p.edges.length - 1 < p.edges.length := Nat.sub_lt hpos Nat.one_pos
    have hlast_odd : Odd (p.edges.length - 1) := by
      obtain ⟨k, hk⟩ := heven
      cases k with
      | zero => omega
      | succ j => exact ⟨j, by omega⟩
    have hlast_in_M := (halt _ hlast_idx).2 hlast_odd
    have hlast_eq := Walk.edges_getElem_eq p _ hlast_idx
    rw [show p.edges.length - 1 + 1 = p.edges.length from by omega] at hlast_eq
    have hgetv : p.getVert p.edges.length = v := by rw [p.length_edges]; exact p.getVert_length
    rw [hgetv] at hlast_eq
    rw [hlast_eq] at hlast_in_M
    rw [Subgraph.mem_edgeSet] at hlast_in_M
    have heqw : w = p.getVert (p.edges.length - 1) :=
      hM.eq_of_adj_left habs hlast_in_M.symm
    rw [heqw] at hw_supp
    exact hw_supp (Walk.getVert_mem_support p _)

end SimpleGraph

namespace SimpleGraph

/--
[konig_cover_isVertexCover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Konig.lean)
-/
@[path]
lemma konig_cover_isVertexCover
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Set V}
  {M : G.Subgraph}
-- given
  (hBip : G.IsBipartiteWith A B)
  (hM : M.IsMatching)
  (hMax : M.IsMaxMatching) :
-- imply
  G.IsVertexCover (konigCover G M A B) := by
-- proof
  open Classical in
  intro v w hadj
  obtain ⟨hvA, hwB⟩ | ⟨hvB, hwA⟩ := hBip.mem_of_adj hadj
  ·
    by_cases hvF : v ∈ alternatingForestSet G M A
    ·
      right; apply Set.mem_union_right
      constructor
      · exact hwB
      ·
        obtain ⟨a, p, haA, haM, hpath, halt⟩ := hvF
        show IsInAlternatingForest G M A w
        by_cases hw_supp : w ∈ p.support
        · exact ⟨a, p.takeUntil w hw_supp, haA, haM,
          hpath.takeUntil hw_supp, alternatingFrom_takeUntil halt hw_supp⟩
        · have hedge_not_M : s(v, w) ∉ M.edgeSet :=
          forest_edge_not_in_M hBip hM haA haM hvA hpath halt hadj hw_supp
          refine ⟨a, p.concat hadj, haA, haM, hpath.concat hw_supp hadj, ?_⟩
          intro i hi
          have hlen : (p.concat hadj).edges.length = p.edges.length + 1 := by
            simp only [Walk.edges_concat, List.length_concat]
          by_cases hi_last : i < p.edges.length
          · have hget : (p.concat hadj).edges[i]'hi = p.edges[i]'hi_last := by
            simp only [Walk.edges_concat, List.concat_eq_append]
            exact List.getElem_append_left hi_last
            rw [hget]; exact halt i hi_last
          · have hi_eq : i = p.edges.length := by omega
            subst hi_eq
            have hget : (p.concat hadj).edges[p.edges.length]'hi = s(v, w) := by
              simp only [Walk.edges_concat, List.concat_eq_append,
                List.getElem_concat_length rfl]
            rw [hget]
            exact ⟨fun _ => hedge_not_M, fun hodd => by
              exfalso
              have heven : Even p.edges.length := by
                by_contra h; rw [Nat.not_even_iff_odd] at h
                exact absurd hvA (Set.disjoint_left.mp hBip.disjoint.symm
                  ((walk_endpoint_parity hBip p).1 haA |>.2 h))
              exact (Nat.not_odd_iff_even.mpr heven) hodd⟩
    ·
      left; exact Set.mem_union_left _ ⟨hvA, hvF⟩
  ·
    by_cases hwF : w ∈ alternatingForestSet G M A
    ·
      left; apply Set.mem_union_right
      constructor
      · exact hvB
      · obtain ⟨a, p, haA, haM, hpath, halt⟩ := hwF
        show IsInAlternatingForest G M A v
        by_cases hv_supp : v ∈ p.support
        · exact ⟨a, p.takeUntil v hv_supp, haA, haM,
          hpath.takeUntil hv_supp, alternatingFrom_takeUntil halt hv_supp⟩
        · have hadj' : G.Adj w v := hadj.symm
          have hedge_not_M : s(w, v) ∉ M.edgeSet :=
            forest_edge_not_in_M hBip hM haA haM hwA hpath halt hadj' hv_supp
          refine ⟨a, p.concat hadj', haA, haM, hpath.concat hv_supp hadj', ?_⟩
          intro i hi
          have hlen : (p.concat hadj').edges.length = p.edges.length + 1 := by
            simp only [Walk.edges_concat, List.length_concat]
          by_cases hi_last : i < p.edges.length
          · have hget : (p.concat hadj').edges[i]'hi = p.edges[i]'hi_last := by
            simp only [Walk.edges_concat, List.concat_eq_append]
            exact List.getElem_append_left hi_last
            rw [hget]; exact halt i hi_last
          · have hi_eq : i = p.edges.length := by omega
            subst hi_eq
            have hget : (p.concat hadj').edges[p.edges.length]'hi = s(w, v) := by
              simp only [Walk.edges_concat, List.concat_eq_append,
                List.getElem_concat_length rfl]
            rw [hget]
            exact ⟨fun _ => hedge_not_M, fun hodd => by
              exfalso
              have heven : Even p.edges.length := by
                by_contra h; rw [Nat.not_even_iff_odd] at h
                exact absurd hwA (Set.disjoint_left.mp hBip.disjoint.symm
                  ((walk_endpoint_parity hBip p).1 haA |>.2 h))
              exact (Nat.not_odd_iff_even.mpr heven) hodd⟩
    ·
      right; exact Set.mem_union_left _ ⟨hwA, hwF⟩

end SimpleGraph

namespace SimpleGraph

/--
[konig_cover_encard_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Konig.lean)
-/
@[path]
lemma konig_cover_encard_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Set V}
  {M : G.Subgraph}
-- given
  (hBip : G.IsBipartiteWith A B)
  (hM : M.IsMatching)
  (hMfin : M.edgeSet.Finite)
  (hMax : M.IsMaxMatching) :
-- imply
  (konigCover G M A B).encard = M.edgeSet.encard := by
-- proof
  classical
  apply le_antisymm
  ·
    have hC_matched : ∀ v ∈ konigCover G M A B, v ∈ M.verts := by
      intro v hv
      obtain ⟨hvA, hvF⟩ | ⟨hvB, hvF⟩ := hv
      · by_contra hvM; exact hvF (unmatched_A_in_forest hvA hvM)
      · by_contra hvM
        exact ((forest_characterization M hM hMfin A B hBip).mp hMax v hvB hvM) hvF
    let f : V → Sym2 V := fun v =>
      if h : v ∈ M.verts then s(v, (hM h).choose) else s(v, v)
    have hf_maps : MapsTo f (konigCover G M A B) M.edgeSet := by
      intro v hv
      have hvM := hC_matched v hv
      simp only [f, dif_pos hvM, Subgraph.mem_edgeSet]
      exact (hM hvM).choose_spec.1
    have hf_inj : InjOn f (konigCover G M A B) := by
      intro v₁ hv₁ v₂ hv₂ heq
      have hv₁M := hC_matched v₁ hv₁
      have hv₂M := hC_matched v₂ hv₂
      simp only [f, dif_pos hv₁M, dif_pos hv₂M] at heq
      have hadj₁ := (hM hv₁M).choose_spec.1
      have hadj₂ := (hM hv₂M).choose_spec.1
      rw [Sym2.eq_iff] at heq
      obtain ⟨rfl, _⟩ | ⟨hv₁w₂, hw₁v₂⟩ := heq
      · rfl
      ·
        exfalso
        have hMadj : M.Adj v₁ v₂ := by
          have := hadj₁; rw [show (hM hv₁M).choose = v₂ from hw₁v₂] at this; exact this
        have hGadj := M.adj_sub hMadj
        obtain ⟨hv₁A, hv₂B⟩ | ⟨hv₁B, hv₂A⟩ := hBip.mem_of_adj hGadj
        ·
          have hv₂F : v₂ ∈ alternatingForestSet G M A := by
            obtain ⟨hv₂A', _⟩ | ⟨_, hv₂F'⟩ := hv₂
            · exact absurd hv₂A' (Set.disjoint_left.mp hBip.disjoint.symm hv₂B)
            · exact hv₂F'
          have hv₁NotF : v₁ ∉ alternatingForestSet G M A := by
            obtain ⟨_, hv₁NF⟩ | ⟨hv₁B', _⟩ := hv₁
            · exact hv₁NF
            · exact absurd hv₁B' (Set.disjoint_left.mp hBip.disjoint hv₁A)
          obtain ⟨a₂, p₂, haA₂, haM₂, hpath₂, halt₂⟩ := hv₂F
          apply hv₁NotF
          show IsInAlternatingForest G M A v₁
          by_cases hv₁_supp : v₁ ∈ p₂.support
          · exact ⟨a₂, p₂.takeUntil v₁ hv₁_supp, haA₂, haM₂,
            hpath₂.takeUntil hv₁_supp, alternatingFrom_takeUntil halt₂ hv₁_supp⟩
          ·
            have hadj_v₂v₁ : G.Adj v₂ v₁ := hGadj.symm
            refine ⟨a₂, p₂.concat hadj_v₂v₁, haA₂, haM₂,
              hpath₂.concat hv₁_supp hadj_v₂v₁, ?_⟩
            intro i hi
            have hlen : (p₂.concat hadj_v₂v₁).edges.length = p₂.edges.length + 1 := by
              simp only [Walk.edges_concat, List.length_concat]
            by_cases hi_last : i < p₂.edges.length
            · have hget : (p₂.concat hadj_v₂v₁).edges[i]'hi = p₂.edges[i]'hi_last := by
              simp only [Walk.edges_concat, List.concat_eq_append]
              exact List.getElem_append_left hi_last
              rw [hget]; exact halt₂ i hi_last
            · have hi_eq : i = p₂.edges.length := by omega
              subst hi_eq
              have hget : (p₂.concat hadj_v₂v₁).edges[p₂.edges.length]'hi = s(v₂, v₁) := by
                simp only [Walk.edges_concat, List.concat_eq_append,
                  List.getElem_concat_length rfl]
              rw [hget]
              constructor
              · intro heven
                exfalso
                have := (walk_endpoint_parity hBip p₂).1 haA₂ |>.1 heven
                exact Set.disjoint_left.mp hBip.disjoint this hv₂B
              · intro _
                rwa [Subgraph.mem_edgeSet]
        ·
          have hv₁F : v₁ ∈ alternatingForestSet G M A := by
            obtain ⟨hv₁A', _⟩ | ⟨_, hv₁F'⟩ := hv₁
            · exact absurd hv₁A' (Set.disjoint_left.mp hBip.disjoint.symm hv₁B)
            · exact hv₁F'
          have hv₂NotF : v₂ ∉ alternatingForestSet G M A := by
            obtain ⟨_, hv₂NF⟩ | ⟨hv₂B', _⟩ := hv₂
            · exact hv₂NF
            · exact absurd hv₂B' (Set.disjoint_left.mp hBip.disjoint hv₂A)
          obtain ⟨a₁, p₁, haA₁, haM₁, hpath₁, halt₁⟩ := hv₁F
          apply hv₂NotF
          show IsInAlternatingForest G M A v₂
          by_cases hv₂_supp : v₂ ∈ p₁.support
          · exact ⟨a₁, p₁.takeUntil v₂ hv₂_supp, haA₁, haM₁,
            hpath₁.takeUntil hv₂_supp, alternatingFrom_takeUntil halt₁ hv₂_supp⟩
          · have hadj_v₁v₂ : G.Adj v₁ v₂ := hGadj
            refine ⟨a₁, p₁.concat hadj_v₁v₂, haA₁, haM₁,
              hpath₁.concat hv₂_supp hadj_v₁v₂, ?_⟩
            intro i hi
            have hlen : (p₁.concat hadj_v₁v₂).edges.length = p₁.edges.length + 1 := by
              simp only [Walk.edges_concat, List.length_concat]
            by_cases hi_last : i < p₁.edges.length
            · have hget : (p₁.concat hadj_v₁v₂).edges[i]'hi = p₁.edges[i]'hi_last := by
              simp only [Walk.edges_concat, List.concat_eq_append]
              exact List.getElem_append_left hi_last
              rw [hget]; exact halt₁ i hi_last
            · have hi_eq : i = p₁.edges.length := by omega
              subst hi_eq
              have hget : (p₁.concat hadj_v₁v₂).edges[p₁.edges.length]'hi = s(v₁, v₂) := by
                simp only [Walk.edges_concat, List.concat_eq_append,
                  List.getElem_concat_length rfl]
              rw [hget]
              constructor
              · intro heven; exfalso
                have := (walk_endpoint_parity hBip p₁).1 haA₁ |>.1 heven
                exact Set.disjoint_left.mp hBip.disjoint this hv₁B
              · intro _
                rwa [Subgraph.mem_edgeSet]
    exact Set.encard_le_encard_of_injOn hf_maps hf_inj
  ·
    exact hM.edgeSet_encard_le_of_isVertexCover (konig_cover_isVertexCover hBip hM hMax)

end SimpleGraph

namespace SimpleGraph

/--
[vertexCoverNum_eq_maxMatching_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Konig.lean)
-/
@[path]
lemma vertexCoverNum_eq_maxMatching_edgeSet
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Set V}
  {M : G.Subgraph}
-- given
  (hBip : G.IsBipartiteWith A B)
  (hM : M.IsMatching)
  (hMfin : M.edgeSet.Finite)
  (hMax : M.IsMaxMatching) :
-- imply
  G.vertexCoverNum = M.edgeSet.encard := by
-- proof
  apply le_antisymm
  · calc G.vertexCoverNum
    ≤ (konigCover G M A B).encard := (konig_cover_isVertexCover hBip hM hMax).vertexCoverNum_le
    _ = M.edgeSet.encard := konig_cover_encard_eq hBip hM hMfin hMax
  · apply le_iInf; intro C; apply le_iInf; intro hC
    exact hM.edgeSet_encard_le_of_isVertexCover hC

end SimpleGraph

namespace SimpleGraph

/--
[konig_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Konig.lean)
-/
@[path]
lemma konig_theorem
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Set V}
  {M : G.Subgraph}
-- given
  (hBip : G.IsBipartiteWith A B)
  (hM : M.IsMatching)
  (hMfin : M.edgeSet.Finite)
  (hMax : M.IsMaxMatching) :
-- imply
  G.matchingNum = G.vertexCoverNum := by
-- proof
  apply le_antisymm
  · exact matchingNum_le_vertexCoverNum
  · rw [vertexCoverNum_eq_maxMatching_edgeSet hBip hM hMfin hMax]
    exact le_iSup₂ (f := fun (M' : G.Subgraph) (_ : M'.IsMatching) => M'.edgeSet.encard) M hM

end SimpleGraph


-- created on 2026-10-23
