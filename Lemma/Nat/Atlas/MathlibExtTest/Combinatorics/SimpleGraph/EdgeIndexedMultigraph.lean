import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Combinatorics.SimpleGraph.EdgeIndexedMultigraph
open MathlibExtTest MathlibExtTest.EdgeIndexedMultigraph
open scoped BigOperators
open SimpleGraph


namespace MathlibExtTest.EdgeIndexedMultigraph

/--
[single_underlying](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma single_underlying : single.underlying = ⊤ := by
  ext u v
  rw [SimpleGraph.EdgeIndexedMultigraph.underlying_adj]
  fin_cases u <;> fin_cases v <;> simp [single, Sym2.eq_swap]

end MathlibExtTest.EdgeIndexedMultigraph

namespace MathlibExtTest.EdgeIndexedMultigraph

/--
[single_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma single_degree (v : Fin 2) : single.degree v = 1 := by
  fin_cases v <;>
    simp [SimpleGraph.EdgeIndexedMultigraph.degree_eq_ncard_inc, single]

end MathlibExtTest.EdgeIndexedMultigraph

namespace MathlibExtTest.EdgeIndexedMultigraph

/--
[double_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma double_degree (v : Fin 2) : double.degree v = 2 := by
  rw [double, SimpleGraph.EdgeIndexedMultigraph.disjointSum_degree,
    single_degree]

end MathlibExtTest.EdgeIndexedMultigraph

namespace MathlibExtTest.EdgeIndexedMultigraph

/--
[double_connected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
private lemma double_connected : double.underlying.Connected := by
  apply SimpleGraph.EdgeIndexedMultigraph.disjointSum_connected_left
  rwa [single_underlying]

end MathlibExtTest.EdgeIndexedMultigraph

namespace MathlibExtTest.EdgeIndexedMultigraph

/--
[indexedEulerian_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeIndexedMultigraph.lean)
-/
@[path]
lemma indexedEulerian_concrete
-- imply
  ∃ (u : Fin 2) (p : double.IndexedWalk u u), p.IsTrail ∧ Sum.inl () ∈ p.edges ∧ Sum.inr () ∈ p.edges := by
-- proof
  obtain ⟨u, p, hp⟩ := double.exists_indexedEulerian double_connected (by
    intro v
    rw [double_degree]
    exact even_two)
  exact ⟨u, p, hp.1, hp.2 (Sum.inl ()), hp.2 (Sum.inr ())⟩

end MathlibExtTest.EdgeIndexedMultigraph


-- created on 2026-10-23
