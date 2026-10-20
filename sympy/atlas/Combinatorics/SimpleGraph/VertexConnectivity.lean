/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Vertex connectivity

A shared vertex-connectivity predicate for finite simple graphs.
-/

namespace SimpleGraph

/-- `IsVertexConnected k G` means that `G` has more than `k` vertices and
stays connected after removing any set of fewer than `k` vertices. -/
def IsVertexConnected {V : Type*} [Fintype V] (k : ℕ) (G : SimpleGraph V) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce (S : Set V)ᶜ).Connected

/-- Characterization of vertex connectivity by deletion of small vertex sets. -/
theorem isVertexConnected_iff {V : Type*} [Fintype V] {k : ℕ} {G : SimpleGraph V} :
    G.IsVertexConnected k ↔
      k < Fintype.card V ∧
        ∀ S : Finset V, S.card < k → (G.induce (S : Set V)ᶜ).Connected :=
  Iff.rfl

/-- A `k`-vertex-connected graph has more than `k` vertices. -/
theorem IsVertexConnected.card_gt {V : Type*} [Fintype V] {k : ℕ}
    {G : SimpleGraph V} (hG : G.IsVertexConnected k) : k < Fintype.card V :=
  hG.1

/-- Deleting fewer than `k` vertices from a `k`-vertex-connected graph leaves a connected
induced graph. -/
theorem IsVertexConnected.connected_induce_compl {V : Type*} [Fintype V] {k : ℕ}
    {G : SimpleGraph V} (hG : G.IsVertexConnected k) (S : Finset V) (hS : S.card < k) :
    (G.induce (S : Set V)ᶜ).Connected :=
  hG.2 S hS

/-- A positively vertex-connected graph is connected. -/
theorem IsVertexConnected.connected {V : Type*} [Fintype V] {k : ℕ}
    {G : SimpleGraph V} (hG : G.IsVertexConnected k) (hk : 0 < k) : G.Connected := by
  have h := hG.connected_induce_compl ∅ (by simpa using hk)
  have hs : (↑(∅ : Finset V) : Set V)ᶜ = Set.univ := by
    ext
    simp
  rw [hs] at h
  exact G.induceUnivIso.connected_iff.mp h

/-- Deleting one vertex from a graph of vertex connectivity at least two leaves a connected
induced graph. -/
theorem IsVertexConnected.connected_compl_singleton {V : Type*} [Fintype V] {k : ℕ}
    {G : SimpleGraph V} (hG : G.IsVertexConnected k) (hk : 1 < k) (v : V) :
    (G.induce (↑({v} : Finset V) : Set V)ᶜ).Connected := by
  classical
  exact hG.connected_induce_compl {v} (by simpa using hk)

/-- A finite graph is 2-vertex-connected exactly when it has at least three vertices, is
connected, and stays connected after deleting each single vertex. -/
theorem isVertexConnected_two_iff {V : Type*} [Fintype V] {G : SimpleGraph V} :
    G.IsVertexConnected 2 ↔
      2 < Fintype.card V ∧ G.Connected ∧
        ∀ v, (G.induce (↑({v} : Finset V) : Set V)ᶜ).Connected := by
  classical
  constructor
  · intro hG
    exact ⟨hG.card_gt, hG.connected (by omega),
      hG.connected_compl_singleton (by omega)⟩
  · rintro ⟨hcard, hconn, hdelete⟩
    refine ⟨hcard, fun S hS ↦ ?_⟩
    have hcardS : S.card = 0 ∨ S.card = 1 := by omega
    rcases hcardS with hzero | hone
    · rw [Finset.card_eq_zero.mp hzero]
      have hs : (↑(∅ : Finset V) : Set V)ᶜ = Set.univ := by simp
      rw [hs]
      exact G.induceUnivIso.connected_iff.mpr hconn
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
      exact hdelete v

/-- Every vertex of a finite 2-vertex-connected graph has degree at least two. -/
theorem IsVertexConnected.two_le_degree {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.IsVertexConnected 2) (v : V) :
    2 ≤ G.degree v := by
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
    rcases ht with rfl | rfl
    · exact huv
    · exact hvzG
  rw [← card_neighborFinset_eq_degree]
  calc
    2 = ({u, (z : V)} : Finset V).card := (Finset.card_pair huz).symm
    _ ≤ (G.neighborFinset v).card := Finset.card_le_card hsub

/-- Every vertex of a finite 2-vertex-connected graph lies on a cycle. -/
theorem IsVertexConnected.exists_cycle_through {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hG : G.IsVertexConnected 2) (x : V) :
    ∃ c : G.Walk x x, c.IsCycle := by
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
  rcases he with he | he
  · exact hx (p.fst_mem_support_of_mem_edges he)
  · rcases Sym2.eq_iff.mp he with ⟨_, hux⟩ | ⟨_, huv'⟩
    · exact hu.ne hux.symm
    · exact huv huv'

end SimpleGraph
