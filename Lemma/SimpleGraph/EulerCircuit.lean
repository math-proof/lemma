import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.EulerCircuit
open SimpleGraph


/--
[Walk.IsEulerian.countP_edges_eq_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EulerCircuit.lean)
-/
@[path]
private lemma Walk_IsEulerian_countP_edges_eq_degree_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {u v : V}
  {p : G.Walk u v}
  {x : V}
-- given
  (hp : p.IsEulerian) :
-- imply
  p.edges.countP (x ∈ ·) = G.degree x := by
-- proof
  apply SimpleGraph.Walk.IsEulerian.countP_edges_eq_degree hp x

/--
[Connected.exists_isEulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EulerCircuit.lean)
-/
@[path]
private lemma Connected_exists_isEulerian_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
-- given
  (hG : G.Connected)
  (heven : ∀ v, Even (G.degree v)) :
-- imply
  ∃ (u : V) (p : G.Walk u u), p.IsEulerian := by
-- proof
  apply SimpleGraph.Connected.exists_isEulerian hG heven

/--
[Reachable.induce_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EulerCircuit.lean)
-/
@[path]
private lemma Reachable_induce_support_eq
  {G : SimpleGraph V}
  {u v : V}
-- given
  (h : G.Reachable u v)
  (hu : u ∈ G.support)
  (hv : v ∈ G.support) :
-- imply
  (G.induce G.support).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply SimpleGraph.Reachable.induce_support h hu hv

/--
[ConnectedSupport.exists_isEulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EulerCircuit.lean)
-/
@[path]
private lemma ConnectedSupport_exists_isEulerian_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
-- given
  (hG : (G.induce G.support).Connected)
  (heven : ∀ v, Even (G.degree v)) :
-- imply
  ∃ (u : V) (p : G.Walk u u), p.IsEulerian := by
-- proof
  apply SimpleGraph.ConnectedSupport.exists_isEulerian hG heven


-- created on 2026-10-20
