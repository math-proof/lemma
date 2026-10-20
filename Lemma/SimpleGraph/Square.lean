import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Square
open SimpleGraph


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
[square_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
private lemma square_mono_eq
  {G H : SimpleGraph V}
-- given
  (hGH : G ≤ H) :
-- imply
  G.square ≤ H.square := by
-- proof
  apply SimpleGraph.square_mono hGH

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

/--
[IsHamiltonian.square_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
private lemma IsHamiltonian_square_mono_eq
  [Fintype V] [DecidableEq V]
  {G H : SimpleGraph V}
-- given
  (hGH : G ≤ H)
  (hG : G.square.IsHamiltonian) :
-- imply
  H.square.IsHamiltonian := by
-- proof
  apply SimpleGraph.IsHamiltonian.square_mono hGH hG

/--
[eq_square_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
private lemma eq_square_iff_eq
  {G H : SimpleGraph V} :
-- imply
  H = G.square ↔
    ∀ u v, H.Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) := by
-- proof
  apply SimpleGraph.eq_square_iff

/--
[isChain_square_of_isChain_cons_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
private lemma isChain_square_of_isChain_cons_cons_eq
  {G : SimpleGraph V}
  {u w v : V}
  {l : List V}
-- given
  (hchain : List.IsChain G.Adj (u :: w :: v :: l))
  (huv : u ≠ v) :
-- imply
  List.IsChain G.square.Adj (u :: v :: l) := by
-- proof
  apply SimpleGraph.isChain_square_of_isChain_cons_cons hchain huv

/--
[IsHamiltonian.square_of_cyclic_list](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
private lemma IsHamiltonian_square_of_cyclic_list_eq
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
  apply SimpleGraph.IsHamiltonian.square_of_cyclic_list G l hne hclosed hsteps hnodup hmem hthree

/--
[IsVertexConnected.four_le_square_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
private lemma IsVertexConnected_four_le_square_degree_eq
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.square.Adj]
  {v : V}
-- given
  (hG : G.IsVertexConnected 2)
  (hcard : 5 ≤ Fintype.card V) :
-- imply
  4 ≤ G.square.degree v := by
-- proof
  apply SimpleGraph.IsVertexConnected.four_le_square_degree hG hcard v


-- created on 2026-10-20
