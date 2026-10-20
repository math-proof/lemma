import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.EdgeIndexedMultigraph
open SimpleGraph
open EdgeIndexedMultigraph
open IndexedWalk


/--
[isTrail_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma isTrail_iff_eq
  {M : EdgeIndexedMultigraph V E}
  {u v : V}
  {p : M.IndexedWalk u v} :
-- imply
  p.IsTrail ↔ p.edges.Nodup := by
-- proof
  apply SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.isTrail_iff M p

/--
[isEulerian_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma isEulerian_iff_eq
  {M : EdgeIndexedMultigraph V E}
  {u v : V}
  {p : M.IndexedWalk u v} :
-- imply
  p.IsEulerian ↔ p.IsTrail ∧ ∀ e, e ∈ p.edges := by
-- proof
  apply SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.isEulerian_iff M p

/--
[support_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma support_nil_eq
  {M : EdgeIndexedMultigraph V E}
  {v : V} :
-- imply
  (IndexedWalk.nil v : M.IndexedWalk v v).support = [v] := by
-- proof
  apply SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.support_nil M v

/--
[support_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma support_cons_eq
  {M : EdgeIndexedMultigraph V E}
  {u v w : V}
  {e : E}
  {p : M.IndexedWalk v w}
-- given
  (he : M.ends e = s(u, v)) :
-- imply
  (IndexedWalk.cons e he p).support = u :: p.support := by
-- proof
  apply SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.support_cons M e he p

/--
[edges_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma edges_nil_eq
  {M : EdgeIndexedMultigraph V E}
  {v : V} :
-- imply
  (IndexedWalk.nil v : M.IndexedWalk v v).edges = [] := by
-- proof
  apply SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.edges_nil M v

/--
[edges_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma edges_cons_eq
  {M : EdgeIndexedMultigraph V E}
  {u v w : V}
  {e : E}
  {p : M.IndexedWalk v w}
-- given
  (he : M.ends e = s(u, v)) :
-- imply
  (IndexedWalk.cons e he p).edges = e :: p.edges := by
-- proof
  apply SimpleGraph.EdgeIndexedMultigraph.IndexedWalk.edges_cons M e he p

/--
[inc_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma inc_iff_eq
  {M : EdgeIndexedMultigraph V E}
  {v : V}
  {e : E} :
-- imply
  M.Inc v e ↔ v ∈ M.ends e := by
-- proof
  apply SimpleGraph.EdgeIndexedMultigraph.inc_iff M v e

/--
[underlying_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma underlying_adj_eq
  {M : EdgeIndexedMultigraph V E}
  {u v : V} :
-- imply
  M.underlying.Adj u v ↔ ∃ e, M.ends e = s(u, v) := by
-- proof
  apply SimpleGraph.underlying_adj M

/--
[support_toWalk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma support_toWalk_eq
  {u v : V}
  {p : M.IndexedWalk u v} :
-- imply
  p.toWalk.support = p.support := by
-- proof
  apply SimpleGraph.IndexedWalk.support_toWalk p

/--
[edges_toWalk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma edges_toWalk_eq
  {M : EdgeIndexedMultigraph V E}
  {u v : V}
  {p : M.IndexedWalk u v} :
-- imply
  p.toWalk.edges = p.edges.map M.ends := by
-- proof
  apply SimpleGraph.IndexedWalk.edges_toWalk M p

/--
[length_toWalk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma length_toWalk_eq
  {M : EdgeIndexedMultigraph V E}
  {u v : V}
  {p : M.IndexedWalk u v} :
-- imply
  p.toWalk.length = p.edges.length := by
-- proof
  apply SimpleGraph.IndexedWalk.length_toWalk M p

/--
[degree_eq_ncard_inc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma degree_eq_ncard_inc_eq
  {M : EdgeIndexedMultigraph V E}
  {v : V} :
-- imply
  M.degree v = {e | M.Inc v e}.ncard := by
-- proof
  apply SimpleGraph.degree_eq_ncard_inc M v

/--
[disjointSum_ends_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma disjointSum_ends_inl_eq
  {M : EdgeIndexedMultigraph V E}
  {N : EdgeIndexedMultigraph V F}
  {e : E} :
-- imply
  (M.disjointSum N).ends (Sum.inl e) = M.ends e := by
-- proof
  apply SimpleGraph.disjointSum_ends_inl M N e

/--
[disjointSum_ends_inr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma disjointSum_ends_inr_eq
  {M : EdgeIndexedMultigraph V E}
  {N : EdgeIndexedMultigraph V F}
  {f : F} :
-- imply
  (M.disjointSum N).ends (Sum.inr f) = N.ends f := by
-- proof
  apply SimpleGraph.disjointSum_ends_inr M N f

/--
[disjointSum_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma disjointSum_degree_eq
  [Finite E] [Finite F]
  {M : EdgeIndexedMultigraph V E}
  {N : EdgeIndexedMultigraph V F}
  {v : V} :
-- imply
  (M.disjointSum N).degree v = M.degree v + N.degree v := by
-- proof
  apply SimpleGraph.disjointSum_degree M N v

/--
[disjointSum_connected_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma disjointSum_connected_left_eq
  {M : EdgeIndexedMultigraph V E}
  {N : EdgeIndexedMultigraph V F}
-- given
  (hM : M.underlying.Connected) :
-- imply
  (M.disjointSum N).underlying.Connected := by
-- proof
  apply SimpleGraph.disjointSum_connected_left M N hM

/--
[even_sum_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma even_sum_degree_eq
  [Fintype V] [Finite E]
  {M : EdgeIndexedMultigraph V E} :
-- imply
  Even (∑ v, M.degree v) := by
-- proof
  apply SimpleGraph.even_sum_degree M

/--
[exists_indexedEulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma exists_indexedEulerian_eq
  [Finite V] [Finite E]
  {M : EdgeIndexedMultigraph V E}
-- given
  (hconn : M.underlying.Connected)
  (heven : ∀ v, Even (M.degree v)) :
-- imply
  ∃ (u : V) (p : M.IndexedWalk u u), p.IsEulerian := by
-- proof
  apply SimpleGraph.exists_indexedEulerian M hconn heven

/--
[exists_indexedEulerian_connectedSupport](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma exists_indexedEulerian_connectedSupport_eq
  [Finite V] [Finite E]
  {M : EdgeIndexedMultigraph V E}
-- given
  (hconn : (M.underlying.induce M.underlying.support).Connected)
  (heven : ∀ v, Even (M.degree v)) :
-- imply
  ∃ (u : V) (p : M.IndexedWalk u u), p.IsEulerian := by
-- proof
  apply SimpleGraph.exists_indexedEulerian_connectedSupport M hconn heven


-- created on 2026-10-20
