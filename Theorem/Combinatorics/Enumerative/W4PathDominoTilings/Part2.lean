/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part4
open SimpleGraph


section

namespace MetaMathlibExt

theorem partner_spec (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (v : Fin 4 × Fin m) :
    M.Adj v (partner m M hM v) := by
  unfold partner
  exact Classical.choose_spec _

theorem partner_unique (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (v w : Fin 4 × Fin m) (h : M.Adj v w) :
    w = partner m M hM v := by
  have hex := Subgraph.isPerfectMatching_iff.mp hM v
  exact hex.unique h (partner_spec m M hM v)

theorem partner_classify (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (a : Fin 4) (i : Fin m) :
    let p := partner m M hM (a, i)
    (W4.Adj a p.1 ∧ i = p.2) ∨ (pathGraph m).Adj i p.2 ∧ a = p.1 := by
  have hadj := partner_spec m M hM (a, i)
  have hg := M.adj_sub hadj
  rw [boxProd_adj] at hg
  exact hg

theorem partner_symm (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (v : Fin 4 × Fin m) :
    partner m M hM (partner m M hM v) = v := by
  have h1 := partner_spec m M hM v
  have h2 := h1.symm
  have h3 := partner_unique m M hM (partner m M hM v) v h2
  exact h3.symm

end MetaMathlibExt
end
