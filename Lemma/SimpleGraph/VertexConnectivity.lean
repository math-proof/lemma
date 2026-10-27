import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
open SimpleGraph


namespace SimpleGraph

/--
[isVertexConnected_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
lemma isVertexConnected_iff
  [Fintype V]
  {k : ℕ}
  {G : SimpleGraph V} :
-- imply
  G.IsVertexConnected k ↔
    k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce (S : Set V)ᶜ).Connected :=
-- proof
  Iff.rfl

end SimpleGraph

namespace SimpleGraph

/--
[IsVertexConnected.card_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
lemma IsVertexConnected.card_gt
  [Fintype V]
  {k : ℕ}
  {G : SimpleGraph V}
-- given
  (hG : G.IsVertexConnected k) :
-- imply
  k < Fintype.card V :=
-- proof
  hG.1

end SimpleGraph

namespace SimpleGraph

/--
[IsVertexConnected.connected_induce_compl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
lemma IsVertexConnected.connected_induce_compl
  [Fintype V]
  {k : ℕ}
  {G : SimpleGraph V}
  {S : Finset V}
-- given
  (hG : G.IsVertexConnected k)
  (hS : S.card < k) :
-- imply
  (G.induce (S : Set V)ᶜ).Connected :=
-- proof
  hG.2 S hS

end SimpleGraph

namespace SimpleGraph

/--
[IsVertexConnected.connected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
lemma IsVertexConnected.connected
  [Fintype V]
  {k : ℕ}
  {G : SimpleGraph V}
-- given
  (hG : G.IsVertexConnected k)
  (hk : 0 < k) :
-- imply
  G.Connected := by
-- proof
  have h := hG.connected_induce_compl ∅ (by simpa using hk)
  have hs : (↑(∅ : Finset V) : Set V)ᶜ = Set.univ := by
    ext
    simp
  rw [hs] at h
  exact G.induceUnivIso.connected_iff.mp h

end SimpleGraph

namespace SimpleGraph

/--
[IsVertexConnected.connected_compl_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
lemma IsVertexConnected.connected_compl_singleton
  [Fintype V]
  {k : ℕ}
  {G : SimpleGraph V}
  {v : V}
-- given
  (hG : G.IsVertexConnected k)
  (hk : 1 < k) :
-- imply
  (G.induce (↑({v} : Finset V) : Set V)ᶜ).Connected := by
-- proof
  classical
  exact hG.connected_induce_compl {v} (by simpa using hk)

end SimpleGraph

namespace SimpleGraph

/--
[IsVertexConnected.two_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
lemma IsVertexConnected.two_le_degree
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {v : V}
-- given
  (hG : G.IsVertexConnected 2) :
-- imply
  2 ≤ G.degree v := by
-- proof
  classical
  have hcard : 2 < Fintype.card V := hG.card_gt
  have hconn : G.Connected := hG.connected (by omega)
  let _ : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, huv⟩ := exists_adj_iff_not_isIsolated.mpr
    (hconn.preconnected.not_isIsolated v)
  have huv_ne : u ≠ v := (G.ne_of_adj huv).symm
  have hrest : ((Finset.univ.erase u).erase v).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
      omega
    · exact Finset.mem_erase.mpr ⟨huv_ne.symm, Finset.mem_univ v⟩
  obtain ⟨w, hw⟩ := hrest
  rw [Finset.mem_erase, Finset.mem_erase] at hw
  let v' : {x : V // x ∈ (↑({u} : Finset V) : Set V)ᶜ} :=
    ⟨v, by simpa using huv_ne.symm⟩
  let w' : {x : V // x ∈ (↑({u} : Finset V) : Set V)ᶜ} :=
    ⟨w, by simpa using hw.2.1⟩
  let _ : Nontrivial {x : V // x ∈ (↑({u} : Finset V) : Set V)ᶜ} :=
    ⟨v', w', by
      intro h
      exact hw.1 (congrArg Subtype.val h).symm⟩
  have hdel := hG.connected_compl_singleton (by omega) u
  obtain ⟨z, hvz⟩ := exists_adj_iff_not_isIsolated.mpr
    (hdel.preconnected.not_isIsolated v')
  have hvzG : G.Adj v z := induce_adj.mp hvz
  have huz : u ≠ z := by
    have hzu : (z : V) ≠ u := by simpa using z.property
    exact hzu.symm
  have hsub : ({u, (z : V)} : Finset V) ⊆ G.neighborFinset v := by
    intro t ht
    rw [Finset.mem_insert, Finset.mem_singleton] at ht
    rw [mem_neighborFinset]
    obtain rfl | rfl := ht
    · exact huv
    · exact hvzG
  rw [← card_neighborFinset_eq_degree]
  calc
    2 = ({u, (z : V)} : Finset V).card := (Finset.card_pair huz).symm
    _ ≤ (G.neighborFinset v).card := Finset.card_le_card hsub

end SimpleGraph

namespace SimpleGraph

/--
[IsVertexConnected.exists_cycle_through](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
lemma IsVertexConnected.exists_cycle_through
  [Fintype V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (hG : G.IsVertexConnected 2) :
-- imply
  ∃ c : G.Walk x x, c.IsCycle := by
-- proof
  classical
  have hcard : 1 < (G.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree]
    have := hG.two_le_degree x
    omega
  obtain ⟨u, v, hu, hv, huv⟩ := Finset.one_lt_card_iff.mp hcard
  rw [mem_neighborFinset] at hu hv
  let s : Set V := (↑({x} : Finset V) : Set V)ᶜ
  let u' : s := ⟨u, by simpa [s] using (G.ne_of_adj hu).symm⟩
  let v' : s := ⟨v, by simpa [s] using (G.ne_of_adj hv).symm⟩
  obtain ⟨q, hq⟩ := (hG.connected_compl_singleton (by omega) x).exists_isPath u' v'
  let p : G.Walk u v := q.map (Embedding.induce s).toHom
  have hp : p.IsPath := hq.map Subtype.val_injective
  have hx : x ∉ p.support := by
    change x ∉ (q.map (Embedding.induce s).toHom).support
    rw [Walk.support_map]
    intro hxmem
    obtain ⟨z, -, hzx⟩ := List.mem_map.mp hxmem
    exact z.property (by simpa [s, hzx])
  let r : G.Walk u x := p.concat hv.symm
  have hr : r.IsPath := hp.concat hx hv.symm
  let c : G.Walk x x := Walk.cons hu r
  refine ⟨c, (Walk.cons_isCycle_iff r hu).mpr ⟨hr, ?_⟩⟩
  intro he
  simp only [r, Walk.edges_concat, List.concat_eq_append, List.mem_append,
    List.mem_singleton] at he
  obtain he | he := he
  · exact hx (p.fst_mem_support_of_mem_edges he)
  · rcases Sym2.eq_iff.mp he with ⟨_, hux⟩ | ⟨_, huv'⟩
    · exact hu.ne hux.symm
    · exact huv huv'

end SimpleGraph

/--
[isVertexConnected_two_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
private lemma isVertexConnected_two_iff_eq
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  G.IsVertexConnected 2 ↔
    2 < Fintype.card V ∧ G.Connected ∧
    ∀ v, (G.induce (↑({v} : Finset V) : Set V)ᶜ).Connected := by
-- proof
  apply SimpleGraph.isVertexConnected_two_iff


-- created on 2026-10-20
-- updated on 2026-10-26
