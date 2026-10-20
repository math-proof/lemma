/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import sympy.atlas.Combinatorics.SimpleGraph.VertexConnectivity
import sympy.atlas.Combinatorics.SimpleGraph.HamiltonianCycle
/-!
# Squares of simple graphs

This file defines the square of a simple graph and proves its basic properties.
-/

namespace SimpleGraph

/-- The square of a simple graph: distinct vertices are adjacent when they are adjacent in the
original graph or have a common neighbor. -/
def square {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.elim (fun huv ↦ Or.inl huv.symm)
    (fun ⟨w, huw, hwv⟩ ↦ Or.inr ⟨w, hwv.symm, huw.symm⟩)⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Adjacency in the square of a simple graph. -/
@[simp]
theorem square_adj {V : Type*} (G : SimpleGraph V) (u v : V) :
    G.square.Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) :=
  Iff.rfl

/-- Taking graph squares is monotone. -/
theorem square_mono {V : Type*} {G H : SimpleGraph V} (hGH : G ≤ H) :
    G.square ≤ H.square := by
  rintro u v ⟨huv, h | ⟨w, huw, hwv⟩⟩
  · exact ⟨huv, Or.inl (hGH h)⟩
  · exact ⟨huv, Or.inr ⟨w, hGH huw, hGH hwv⟩⟩

/-- The square of a connected graph is connected. -/
theorem Connected.square {V : Type*} {G : SimpleGraph V} (hG : G.Connected) :
    G.square.Connected :=
  hG.mono fun _ _ h ↦ ⟨G.ne_of_adj h, Or.inl h⟩

/-- A Hamiltonian square remains Hamiltonian after edges are added to the original graph. -/
theorem IsHamiltonian.square_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H) (hG : G.square.IsHamiltonian) : H.square.IsHamiltonian :=
  hG.mono (SimpleGraph.square_mono hGH)

/-- A graph is the square of `G` exactly when it has the expected adjacency relation. -/
theorem eq_square_iff {V : Type*} {G H : SimpleGraph V} :
    H = G.square ↔
      ∀ u v, H.Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) := by
  constructor
  · rintro rfl u v
    exact square_adj G u v
  · intro h
    ext u v
    exact h u v

/-- Replacing two consecutive edges by their endpoints preserves a chain in the graph square. -/
theorem isChain_square_of_isChain_cons_cons {V : Type*} {G : SimpleGraph V}
    {u w v : V} {l : List V} (hchain : List.IsChain G.Adj (u :: w :: v :: l))
    (huv : u ≠ v) : List.IsChain G.square.Adj (u :: v :: l) := by
  have huw := (List.isChain_cons_cons.mp hchain).1
  have hrest := (List.isChain_cons_cons.mp hchain).2
  have hwv := (List.isChain_cons_cons.mp hrest).1
  have htail := (List.isChain_cons_cons.mp hrest).2
  rw [List.isChain_cons_cons]
  refine ⟨⟨huv, Or.inr ⟨w, huw, hwv⟩⟩, ?_⟩
  exact htail.imp fun ⦃_ _⦄ hab ↦ ⟨G.ne_of_adj hab, Or.inl hab⟩

/-- Shortcutting length-two steps in a closed cyclic listing produces a Hamiltonian cycle in the
square. -/
theorem IsHamiltonian.square_of_cyclic_list {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (l : List V) (hne : l ≠ [])
    (hclosed : l.head hne = l.getLast hne)
    (hsteps : l.IsChain fun u v ↦
      u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v))
    (hnodup : l.tail.Nodup) (hmem : ∀ v, v ∈ l.tail)
    (hthree : 3 ≤ l.length - 1) : G.square.IsHamiltonian := by
  apply IsHamiltonian.of_cyclic_list G.square l hne hclosed
  · exact hsteps
  · exact hnodup
  · exact hmem
  · exact hthree

/-- In a 2-vertex-connected graph on at least five vertices, every vertex has at least four
neighbors in the graph square. -/
theorem IsVertexConnected.four_le_square_degree
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.square.Adj] (hG : G.IsVertexConnected 2)
    (hcard : 5 ≤ Fintype.card V) (v : V) : 4 ≤ G.square.degree v := by
  classical
  have hdeg : 2 ≤ G.degree v := hG.two_le_degree v
  by_contra hfour
  have hsdeg : G.square.degree v ≤ 3 := by omega
  set N := G.neighborFinset v with hNdef
  set S := G.square.neighborFinset v with hSdef
  set T := S \ N with hTdef
  have hNS : N ⊆ S := by
    intro u hu
    rw [hNdef, mem_neighborFinset] at hu
    rw [hSdef, mem_neighborFinset]
    exact ⟨G.ne_of_adj hu, Or.inl hu⟩
  have hNcard : N.card = G.degree v := card_neighborFinset_eq_degree G v
  have hScard : S.card = G.square.degree v := card_neighborFinset_eq_degree G.square v
  have hTcard : T.card < 2 := by
    rw [hTdef, Finset.card_sdiff_of_subset hNS, hNcard, hScard]
    omega
  have hdel := hG.connected_induce_compl T hTcard
  have hvS : v ∉ S := by
    rw [hSdef, mem_neighborFinset]
    exact G.square.loopless.1 v
  have hcard_insert : (insert v S).card = S.card + 1 := Finset.card_insert_of_notMem hvS
  have hsmall : (insert v S).card < Fintype.card V := by
    rw [hcard_insert, hScard]
    omega
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ insert v S := by
    by_contra! hall
    have huniv : insert v S = Finset.univ := Finset.eq_univ_of_forall hall
    have hc := congrArg Finset.card huniv
    simp only [Finset.card_univ] at hc
    omega
  have hvT : v ∉ T := by
    intro hv
    exact hvS (Finset.mem_sdiff.mp hv).1
  have hwS : w ∉ S := fun h ↦ hw (Finset.mem_insert_of_mem h)
  have hwT : w ∉ T := by
    intro h
    exact hwS (Finset.mem_sdiff.mp h).1
  let v' : {x : V // x ∈ (↑T : Set V)ᶜ} := ⟨v, by simpa using hvT⟩
  let w' : {x : V // x ∈ (↑T : Set V)ᶜ} := ⟨w, by simpa using hwT⟩
  set A := insert v N with hAdef
  have hvA : v ∈ A := Finset.mem_insert_self v N
  have hwA : w ∉ A := by
    intro h
    rw [hAdef, Finset.mem_insert] at h
    rcases h with hwv | hN
    · exact hw (hwv ▸ Finset.mem_insert_self v S)
    · exact hwS (hNS hN)
  have hclosed : ∀ (x y : {z : V // z ∈ (↑T : Set V)ᶜ}),
      x.1 ∈ A → (G.induce (↑T : Set V)ᶜ).Adj x y → y.1 ∈ A := by
    intro x y hx hxy
    have hxyG : G.Adj x y := induce_adj.mp hxy
    rw [hAdef, Finset.mem_insert] at hx ⊢
    rcases hx with hx | hx
    · right
      rw [hx] at hxyG
      rw [hNdef, mem_neighborFinset]
      exact hxyG
    · by_cases hyv : (y : V) = v
      · exact Or.inl hyv
      · right
        have hvx : G.Adj v x := by
          rw [← mem_neighborFinset]
          exact hx
        have hyS : (y : V) ∈ S := by
          rw [hSdef, mem_neighborFinset]
          exact ⟨Ne.symm hyv, Or.inr ⟨x, hvx, hxyG⟩⟩
        have hyT : (y : V) ∉ T := by
          have h := y.property
          change (y : V) ∉ T at h
          exact h
        by_contra hyN
        exact hyT (Finset.mem_sdiff.mpr ⟨hyS, hyN⟩)
  have hwalk_closed : ∀ (x y : {z : V // z ∈ (↑T : Set V)ᶜ})
      (p : (G.induce (↑T : Set V)ᶜ).Walk x y), x.1 ∈ A → y.1 ∈ A := by
    intro x y p hx
    induction p with
    | nil => exact hx
    | @cons _ _ _ h p ih => exact ih (hclosed _ _ hx h)
  obtain ⟨p⟩ := hdel v' w'
  exact hwA (hwalk_closed v' w' p hvA)

end SimpleGraph
