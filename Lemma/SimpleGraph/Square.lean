import Mathlib
import sympy.Basic
import Theorem.Combinatorics.SimpleGraph.Square
open SimpleGraph


namespace SimpleGraph

/--
[square_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
lemma square_mono
  {G H : SimpleGraph V}
-- given
  (hGH : G ≤ H) :
-- imply
  G.square ≤ H.square := by
-- proof
  rintro u v ⟨huv, h | ⟨w, huw, hwv⟩⟩
  · exact ⟨huv, Or.inl (hGH h)⟩
  · exact ⟨huv, Or.inr ⟨w, hGH huw, hGH hwv⟩⟩

end SimpleGraph

namespace SimpleGraph

/--
[IsHamiltonian.square_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
lemma IsHamiltonian.square_mono
  [Fintype V] [DecidableEq V]
  {G H : SimpleGraph V}
-- given
  (hGH : G ≤ H)
  (hG : G.square.IsHamiltonian) :
-- imply
  H.square.IsHamiltonian :=
-- proof
  hG.mono (SimpleGraph.square_mono hGH)

end SimpleGraph

namespace SimpleGraph

/--
[isChain_square_of_isChain_cons_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
lemma isChain_square_of_isChain_cons_cons
  {G : SimpleGraph V}
  {u w v : V}
  {l : List V}
-- given
  (hchain : List.IsChain G.Adj (u :: w :: v :: l))
  (huv : u ≠ v) :
-- imply
  List.IsChain G.square.Adj (u :: v :: l) := by
-- proof
  have huw := (List.isChain_cons_cons.mp hchain).1
  have hrest := (List.isChain_cons_cons.mp hchain).2
  have hwv := (List.isChain_cons_cons.mp hrest).1
  have htail := (List.isChain_cons_cons.mp hrest).2
  rw [List.isChain_cons_cons]
  refine ⟨⟨huv, Or.inr ⟨w, huw, hwv⟩⟩, ?_⟩
  exact htail.imp fun ⦃_ _⦄ hab ↦ ⟨G.ne_of_adj hab, Or.inl hab⟩

end SimpleGraph

namespace SimpleGraph

/--
[IsHamiltonian.square_of_cyclic_list](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
lemma IsHamiltonian.square_of_cyclic_list
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}
  {l : List V}
-- given
  (hne : l ≠ [])
  (hclosed : l.head hne = l.getLast hne)
  (hsteps : l.IsChain fun u v ↦ u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v))
  (hnodup : l.tail.Nodup)
  (hmem : ∀ v, v ∈ l.tail)
  (hthree : 3 ≤ l.length - 1) :
-- imply
  G.square.IsHamiltonian := by
-- proof
  apply IsHamiltonian.of_cyclic_list G.square l hne hclosed
  · exact hsteps
  · exact hnodup
  · exact hmem
  · exact hthree

end SimpleGraph

/--
[eq_square_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
lemma eq_square_iff
  {G H : SimpleGraph V} :
-- imply
  H = G.square ↔
    ∀ u v, H.Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) := by
-- proof
  constructor
  · rintro rfl u v
    exact square_adj G u v
  · intro h
    ext u v
    exact h u v


namespace SimpleGraph

/--
[IsVertexConnected.four_le_square_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
lemma IsVertexConnected.four_le_square_degree
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.square.Adj]
  {v : V}
-- given
  (hG : G.IsVertexConnected 2)
  (hcard : 5 ≤ Fintype.card V) :
-- imply
  4 ≤ G.square.degree v := by
-- proof
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
    obtain hwv | hN := h
    · exact hw (hwv ▸ Finset.mem_insert_self v S)
    · exact hwS (hNS hN)
  have hclosed : ∀ (x y : {z : V // z ∈ (↑T : Set V)ᶜ}),
    x.1 ∈ A → (G.induce (↑T : Set V)ᶜ).Adj x y → y.1 ∈ A := by
    intro x y hx hxy
    have hxyG : G.Adj x y := induce_adj.mp hxy
    rw [hAdef, Finset.mem_insert] at hx ⊢
    obtain hx | hx := hx
    · right
      rw [hx] at hxyG
      rwa [hNdef, mem_neighborFinset]
    · by_cases hyv : (y : V) = v
      · exact Or.inl hyv
      · right
        have hvx : G.Adj v x := by
          rwa [← mem_neighborFinset]
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

/--
[square_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
private lemma square_adj_eq
  {G : SimpleGraph V}
  {u v : V} :
-- imply
  G.square.Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) := by
-- proof
  apply SimpleGraph.square_adj G u v

/--
[Connected.square](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
private lemma Connected_square_eq
  {G : SimpleGraph V}
-- given
  (hG : G.Connected) :
-- imply
  G.square.Connected := by
-- proof
  apply SimpleGraph.Connected.square hG


-- created on 2026-10-20
-- updated on 2026-10-23
