import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.PerfectGraph
open scoped Matrix BigOperators
open scoped Classical in s.map ⟨Subtype.val, Subtype.val_injective⟩
open MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted


/--
[lovasz_weak_perfect_graph_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/PerfectGraph.lean)
-/
@[path]
private lemma lovasz_weak_perfect_graph_general_eq
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  IsPerfect G ↔ IsPerfect Gᶜ := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.lovasz_weak_perfect_graph_general G

/--
[lovasz_weak_perfect_graph](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/PerfectGraph.lean)
-/
@[path]
private lemma lovasz_weak_perfect_graph_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  IsPerfect G ↔ IsPerfect Gᶜ := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.lovasz_weak_perfect_graph G


-- created on 2026-10-20
