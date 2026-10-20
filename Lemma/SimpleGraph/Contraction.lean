import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Contraction
open SimpleGraph


/--
[collapseOutside_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma collapseOutside_of_mem_eq
  {D : Set V}
  {v : V}
-- given
  (hv : v ∈ D) :
-- imply
  collapseOutside D v = some ⟨v, hv⟩ := by
-- proof
  apply SimpleGraph.collapseOutside_of_mem D hv

/--
[collapseOutside_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma collapseOutside_of_notMem_eq
  {D : Set V}
  {v : V}
-- given
  (hv : v ∉ D) :
-- imply
  collapseOutside D v = none := by
-- proof
  apply SimpleGraph.collapseOutside_of_notMem D hv

/--
[collapseOutside_eq_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma collapseOutside_eq_some_iff_eq
  {D : Set V}
  {v : V}
  {a : D} :
-- imply
  collapseOutside D v = some a ↔ v = a := by
-- proof
  apply SimpleGraph.collapseOutside_eq_some_iff D v a

/--
[collapseOutside_eq_none_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma collapseOutside_eq_none_iff_eq
  {D : Set V}
  {v : V} :
-- imply
  collapseOutside D v = none ↔ v ∉ D := by
-- proof
  apply SimpleGraph.collapseOutside_eq_none_iff D v

/--
[collapseOutside_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma collapseOutside_surjective_eq
  {D : Set V}
-- given
  (hD : Dᶜ.Nonempty) :
-- imply
  Function.Surjective (collapseOutside D) := by
-- proof
  apply SimpleGraph.collapseOutside_surjective hD

/--
[contractOutside_adj_some](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma contractOutside_adj_some_eq
  {G : SimpleGraph V}
  {D : Set V}
  {a b : D} :
-- imply
  (G.contractOutside D).Adj (some a) (some b) ↔ G.Adj a b := by
-- proof
  apply SimpleGraph.contractOutside_adj_some G D a b

/--
[contractOutside_adj_none](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma contractOutside_adj_none_eq
  {G : SimpleGraph V}
  {D : Set V}
  {a : D} :
-- imply
  (G.contractOutside D).Adj (some a) none ↔ ∃ v ∉ D, G.Adj a v := by
-- proof
  apply SimpleGraph.contractOutside_adj_none G D a

/--
[IsVertexConnected.contractOutside](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma IsVertexConnected_contractOutside_eq
  [Fintype V]
  {G : SimpleGraph V}
  {D : Set V} [Fintype D]
-- given
  (hG : G.IsVertexConnected 2)
  (hDcard : 1 < Fintype.card D)
  (hDconn : (G.induce D).Connected)
  (hDout : Dᶜ.Nonempty) :
-- imply
  (G.contractOutside D).IsVertexConnected 2 := by
-- proof
  apply SimpleGraph.IsVertexConnected.contractOutside hG hDcard hDconn hDout

/--
[card_contractOutside_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
private lemma card_contractOutside_lt_eq
  [Fintype V] [Fintype ↥(Dᶜ : Set V)]
  {D : Set V} [Fintype D]
-- given
  (hD : 2 ≤ Fintype.card ↥(Dᶜ : Set V)) :
-- imply
  Fintype.card (Option D) < Fintype.card V := by
-- proof
  apply SimpleGraph.card_contractOutside_lt D hD


-- created on 2026-10-20
